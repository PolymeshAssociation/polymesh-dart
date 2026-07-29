use super::{AuthDevice, account_state_from_pubkeys, host_generators};
use crate::account_reg_split::AccountRegHostProtocol;
use crate::affirmation_proofs::SenderAffirmationHostProtocol;
use crate::curve_tree::{AccountTreeConfig, CurveTreeConfig, CurveTreeLookup, ProverCurveTree};
use crate::mint_split::MintHostProtocol;
use crate::{
    ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountKeys, AccountPublicKey,
    AccountPublicKeys, AccountStateCommitment, AssetId, Balance, EncryptionPublicKey, Leg,
    LegConfig, LegEncrypted, LegRef, PallasA, SettlementRef,
};
use polymesh_dart_common::NullifierSkGenCounter;
use rand_chacha::ChaCha20Rng;
use rand_core::{CryptoRngCore, SeedableRng};

/// Builds an encrypted leg and a single-leaf account tree for the affirmation step.
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

/// Runs the full register -> mint -> affirm workflow against `device`, verifying each proof.
pub fn run_register_mint_affirm<D: AuthDevice>(device: &mut D) {
    let mut rng = ChaCha20Rng::seed_from_u64(0);
    let identity: &[u8] = b"test";
    let asset_id: AssetId = 1;
    let counter: NullifierSkGenCounter = 0;

    let tree_params = AccountTreeConfig::parameters();
    let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

    // Provision the device and generate the account keys inside it.
    device
        .setup_params(host_generators(comm_re_rand_gen).unwrap())
        .unwrap();
    let (pubkeys, _sealed) = device.generate_keys().unwrap();
    let pk_aff = PallasA::try_from(&pubkeys.pk_aff).unwrap();
    let pk_enc = PallasA::try_from(&pubkeys.pk_enc).unwrap();

    // Registration
    let (account_state, rho_randomness) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, asset_id, counter, identity).unwrap();
    let (protocol, request) =
        AccountRegHostProtocol::init(&mut rng, &account_state, rho_randomness, counter, identity)
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
        .verify(identity, AccountTreeConfig::parameters(), &mut rng)
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
    let response = device.affirm(request).unwrap();
    let affirm_proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    let root = account_tree.root().unwrap();
    affirm_proof.verify(&leg_enc, &root, &mut rng).unwrap();
}
