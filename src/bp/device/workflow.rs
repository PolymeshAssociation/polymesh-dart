use super::{
    AuthDevice, account_state_from_pubkeys, account_state_from_pubkeys_given_randomness,
    fee_account_state_from_pubkey_given_randomness,
};
use crate::AssetPkTLookup;
use crate::account_reg_split::AccountRegHostProtocol;
use crate::affirmation_proofs::SenderAffirmationHostProtocol;
use crate::curve_tree::{
    AccountTreeConfig, CurveTreeConfig, CurveTreeLookup, FeeAccountTreeConfig, ProverCurveTree,
};
use crate::fee_split::{FeePaymentHostProtocol, FeeRegHostProtocol, FeeTopupHostProtocol};
use crate::key_reg_split::KeyRegistrationDeviceRequest;
use crate::mint_split::MintHostProtocol;
use crate::split_types::AccountRandomnessDeviceRequest;
use crate::{
    ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountKeys, AccountPublicKey,
    AccountPublicKeys, AccountStateCommitment, AssetId, Balance, EncryptionPublicKey,
    FEE_ACCOUNT_TREE_HEIGHT, FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FEE_ASSET_ID, Leg, LegConfig,
    LegEncrypted, LegRef, PallasA, SettlementRef, dart_gens,
};
use codec::Encode;
use polymesh_dart_common::NullifierSkGenCounter;
use rand_chacha::ChaCha20Rng;
use rand_core::{CryptoRngCore, SeedableRng};

fn make_leg_and_tree<R: CryptoRngCore>(
    rng: &mut R,
    sender_enc: EncryptionPublicKey,
    receiver_enc: EncryptionPublicKey,
    asset_id: AssetId,
    amount: Balance,
    state_leaf: AccountStateCommitment,
) -> (
    LegEncrypted,
    LegRef,
    ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
) {
    let leg = Leg::new(sender_enc, receiver_enc, asset_id, amount).unwrap();
    let (_, leg_enc, _) = leg
        .encrypt(rng, LegConfig::default().into(), vec![], vec![], vec![])
        .unwrap();
    let leg_ref = LegRef::new(SettlementRef([1; 32]), 0);
    let mut tree = ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
        ACCOUNT_TREE_HEIGHT,
    )
    .unwrap();
    tree.insert(state_leaf.as_leaf_value().unwrap()).unwrap();
    tree.store_root().unwrap();
    (leg_enc, leg_ref, tree)
}

/// Runs the full key-registration -> account-asset registration -> mint -> affirm workflow against
/// `device`, verifying each proof.
pub fn run_register_mint_affirm<D: AuthDevice>(device: &mut D) {
    let mut rng = ChaCha20Rng::seed_from_u64(0);
    let identity: &[u8] = b"test";
    let asset_id: AssetId = 1;
    let counter: NullifierSkGenCounter = 0;

    // Generate the account keys inside the device.
    let (pubkeys, _) = device.generate_keys().unwrap();
    let pk_aff = PallasA::try_from(&pubkeys.pk_aff).unwrap();
    let pk_enc = PallasA::try_from(&pubkeys.pk_enc).unwrap();

    // Key registration (investor keys). Self-contained on the device — no host protocol.
    let gens = dart_gens();
    let key_reg_response = device
        .key_registration(KeyRegistrationDeviceRequest {
            identity: identity.to_vec(),
        })
        .unwrap();
    let reg_pub_keys: Vec<(PallasA, PallasA)> = key_reg_response
        .accounts
        .iter()
        .map(|(a, e)| (PallasA::try_from(a).unwrap(), PallasA::try_from(e).unwrap()))
        .collect();
    key_reg_response
        .inner
        .decode()
        .unwrap()
        .verify(
            reg_pub_keys,
            identity,
            gens.sig_key_gen(),
            gens.enc_key_gen(),
        )
        .unwrap();

    // Account-asset registration, with the account randomness derived on the device.
    let randomness = device
        .account_randomness(AccountRandomnessDeviceRequest { asset_id, counter })
        .unwrap();
    let (account_state, rho_randomness) = account_state_from_pubkeys_given_randomness(
        pk_aff,
        pk_enc,
        asset_id,
        counter,
        identity,
        &randomness,
    )
    .unwrap();
    let (protocol, request) = AccountRegHostProtocol::init(
        &mut rng,
        &account_state,
        rho_randomness,
        counter,
        identity,
        None,
    )
    .unwrap();
    let response = device.registration_proof(request).unwrap();
    let reg_proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &response,
            counter,
            AccountTreeConfig::parameters(),
        )
        .unwrap();
    reg_proof
        .verify(
            identity,
            AccountTreeConfig::parameters(),
            &mut rng,
            &AssetPkTLookup::default(),
        )
        .unwrap();

    // Mint
    let mut account_state = account_state;
    let mut account_tree =
        ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
            ACCOUNT_TREE_HEIGHT,
        )
        .unwrap();
    account_tree
        .insert(
            account_state
                .current_commitment()
                .unwrap()
                .as_leaf_value()
                .unwrap(),
        )
        .unwrap();
    account_tree.store_root().unwrap();
    let pk = AccountPublicKeys {
        acct: AccountPublicKey::from_affine(pk_aff).unwrap(),
        enc: EncryptionPublicKey::from_affine(pk_enc).unwrap(),
    };
    let mint_amount = 1000;
    let (protocol, request) = MintHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &pk,
        &mut account_state,
        mint_amount,
        identity,
        &account_tree,
    )
    .unwrap();
    let response = device.mint_proof(request).unwrap();
    let root_block = account_tree.get_block_number().unwrap();
    let mint_proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &response,
            root_block,
            AccountTreeConfig::parameters(),
        )
        .unwrap();
    mint_proof
        .verify(identity, account_tree.root().unwrap(), &mut rng)
        .unwrap();

    // Sender affirmation
    let receiver = AccountKeys::rand(&mut rng).unwrap();
    let (mut sender_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, asset_id, counter, identity).unwrap();
    sender_state.current_state.balance = mint_amount;
    let leaf = sender_state.current_commitment().unwrap();
    let send_amount = 300;
    let (leg_enc, leg_ref, account_tree) = make_leg_and_tree(
        &mut rng,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        receiver.enc.public,
        asset_id,
        send_amount,
        leaf,
    );
    let (protocol, request) = SenderAffirmationHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut sender_state,
        &leg_ref,
        &leg_enc,
        send_amount,
        &account_tree,
    )
    .unwrap();
    println!("AFFIRM_REQUEST = {} bytes", request.encode().len());
    let response = device.affirm(request).unwrap();
    println!("AFFIRM_RESPONSE = {} bytes", response.encode().len());
    let affirm_proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    let root = account_tree.root().unwrap();
    affirm_proof.verify(&leg_enc, &root, &mut rng).unwrap();
}

/// Runs the fee account registration -> topup -> payment workflow against `device`, verifying each
/// proof.
pub fn run_fee_register_topup_pay<D: AuthDevice>(device: &mut D) {
    let mut rng = ChaCha20Rng::seed_from_u64(0);
    let identity: &[u8] = b"test";
    let tree_params = FeeAccountTreeConfig::parameters();

    let (pubkeys, _) = device.generate_keys().unwrap();
    let pk = AccountPublicKey::from_affine(PallasA::try_from(&pubkeys.pk_aff).unwrap()).unwrap();

    // Registration, with the fee account randomness derived on the device.
    let randomness = device
        .fee_account_randomness(AccountRandomnessDeviceRequest {
            asset_id: FEE_ASSET_ID,
            counter: 0,
        })
        .unwrap();
    let mut fee_state =
        fee_account_state_from_pubkey_given_randomness(&pk, FEE_ASSET_ID, 1000, &randomness)
            .unwrap();
    let (protocol, request) =
        FeeRegHostProtocol::init(&mut rng, &pk, &fee_state, identity).unwrap();
    println!(
        "FEE_REGISTRATION_REQUEST = {} bytes",
        request.encode().len()
    );
    let response = device.fee_registration_proof(request).unwrap();
    println!(
        "FEE_REGISTRATION_RESPONSE = {} bytes",
        response.encode().len()
    );
    let reg_proof = protocol.finish::<()>(&response).unwrap();
    reg_proof.verify(identity).unwrap();

    let mut fee_tree =
        ProverCurveTree::<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>::new(
            FEE_ACCOUNT_TREE_HEIGHT,
        )
        .unwrap();
    fee_tree
        .insert(reg_proof.account_state_commitment.as_leaf_value().unwrap())
        .unwrap();
    fee_tree.store_root().unwrap();

    // Topup
    let (protocol, request) = FeeTopupHostProtocol::<FeeAccountTreeConfig>::init(
        &mut rng,
        &pk,
        &mut fee_state,
        500,
        identity,
        &fee_tree,
    )
    .unwrap();
    println!("FEE_TOPUP_REQUEST = {} bytes", request.encode().len());
    let response = device.fee_topup_proof(request).unwrap();
    println!("FEE_TOPUP_RESPONSE = {} bytes", response.encode().len());
    let topup_proof = protocol
        .finish::<_, ()>(&mut rng, &response, tree_params)
        .unwrap();
    let root = fee_tree.root().unwrap().root_node().unwrap();
    topup_proof.verify(&mut rng, identity, &root).unwrap();
    fee_state.commit_pending_state().unwrap();
    fee_tree
        .insert(
            topup_proof
                .updated_account_state_commitment
                .as_leaf_value()
                .unwrap(),
        )
        .unwrap();
    fee_tree.store_root().unwrap();

    // Payment
    let (protocol, request) = FeePaymentHostProtocol::<FeeAccountTreeConfig>::init(
        &mut rng,
        &mut fee_state,
        100,
        identity,
        &fee_tree,
    )
    .unwrap();
    println!("FEE_PAYMENT_REQUEST = {} bytes", request.encode().len());
    let response = device.fee_payment_proof(request).unwrap();
    println!("FEE_PAYMENT_RESPONSE = {} bytes", response.encode().len());
    let root_block = fee_tree.get_block_number().unwrap();
    let payment_proof = protocol
        .finish::<_, ()>(&mut rng, &response, root_block, tree_params)
        .unwrap();
    payment_proof
        .verify(&mut rng, identity, fee_tree.root().unwrap())
        .unwrap();
}
