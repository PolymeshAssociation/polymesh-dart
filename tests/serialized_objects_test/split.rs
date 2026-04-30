use polymesh_dart::account_reg_split::AccountRegHostProtocol;
use polymesh_dart::affirmation_proofs::{
    ClaimReceivedHostProtocol, InstantReceiverAffirmationHostProtocol,
    InstantSenderAffirmationHostProtocol, ReceiverAffirmationHostProtocol,
    ReceiverCounterUpdateHostProtocol, SenderAffirmationHostProtocol,
    SenderCounterUpdateHostProtocol, SenderReverseHostProtocol,
};
use polymesh_dart::auth_proofs::{
    create_affirmation_auth_proof, create_fee_account_auth_proof, create_fee_payment_auth_proof,
    create_registration_auth_proof,
};
use polymesh_dart::curve_tree::{
    AccountTreeConfig, CurveTreeConfig, CurveTreeLookup, FeeAccountTreeConfig, ProverCurveTree,
};
use polymesh_dart::fee_split::{FeePaymentHostProtocol, FeeRegHostProtocol, FeeTopupHostProtocol};
use polymesh_dart::mint_split::MintHostProtocol;
use polymesh_dart::split_types::{
    AffirmationDeviceRequest, AffirmationDeviceResponse, FeeAccountDeviceRequest,
    FeePaymentDeviceRequest, FeePaymentDeviceResponse, RegistrationDeviceRequest,
    SingleSkDeviceResponse, TwoSksDeviceResponse,
};
use polymesh_dart::*;
use polymesh_dart_bp::account::state::AccountCommitmentKeyTrait;
use polymesh_dart_common::NullifierSkGenCounter;

use crate::constants::*;
use crate::utils::{alice_keys, bob_keys, default_rng, load_scale_v1, save_scale_v1};

type FeeProverTree = ProverCurveTree<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>;
type AccountProverTree = ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>;

fn make_fee_state_and_tree(keys: &AccountKeys) -> (FeeProverTree, FeeAccountAssetState) {
    let mut rng = default_rng();
    let fee_state =
        FeeAccountAssetState::new(&mut rng, &keys.acct.public, ASSET_ID_1, BALANCE).unwrap();
    let mut tree = FeeProverTree::new(FEE_ACCOUNT_TREE_HEIGHT).unwrap();
    let leaf = fee_state
        .current_commitment()
        .unwrap()
        .as_leaf_value()
        .unwrap();
    tree.insert(leaf).unwrap();
    tree.store_root().unwrap();
    (tree, fee_state)
}

fn make_fee_state_and_tree_after_topup(
    keys: &AccountKeys,
) -> (FeeProverTree, FeeAccountAssetState) {
    let mut rng = default_rng();
    let (mut tree, mut fee_state) = make_fee_state_and_tree(keys);
    let topup_proof = FeeAccountTopupProof::<()>::new(
        &mut rng,
        &keys.acct,
        &mut fee_state,
        TOPUP_AMOUNT,
        IDENTITY,
        &tree,
    )
    .unwrap();
    fee_state.commit_pending_state().unwrap();
    let updated_leaf = topup_proof
        .updated_account_state_commitment
        .as_leaf_value()
        .unwrap();
    tree.insert(updated_leaf).unwrap();
    tree.store_root().unwrap();
    (tree, fee_state)
}

fn make_account_tree(leaf: AccountStateCommitment) -> AccountProverTree {
    let mut tree = AccountProverTree::new(ACCOUNT_TREE_HEIGHT).unwrap();
    tree.insert(leaf.as_leaf_value().unwrap()).unwrap();
    tree.store_root().unwrap();
    tree
}

/// Build a hidden-asset-id `LegEncrypted` (reveal_asset_id = false, parties see each other).
fn make_hidden_asset_leg_enc(
    sender_enc: EncryptionPublicKey,
    receiver_enc: EncryptionPublicKey,
    asset_id: AssetId,
    amount: Balance,
) -> (LegEncrypted, LegRef) {
    let mut rng = default_rng();
    let leg = Leg::new(sender_enc, receiver_enc, asset_id, amount).unwrap();
    let (_, leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegConfig {
                reveal_asset_id: false,
                parties_see_each_other: true,
            }
            .into(),
            vec![],
            vec![],
            vec![],
        )
        .unwrap();
    let leg_ref = LegRef::new(SettlementRef([1u8; 32]), 0);
    (leg_enc, leg_ref)
}

fn make_affirmation_device_response(
    keys: &AccountKeys,
    request: &AffirmationDeviceRequest,
    tree: &AccountProverTree,
) -> AffirmationDeviceResponse {
    let mut rng = default_rng();
    let gens = dart_gens();
    let comm_re_rand_gen = tree.params().even_parameters.pc_gens().B_blinding;
    create_affirmation_auth_proof(
        &mut rng,
        keys,
        request,
        gens.account_comm_key().sk_gen(),
        gens.enc_key_gen(),
        comm_re_rand_gen,
        gens.leg_asset_value_gen(),
    )
    .unwrap()
}

/// Simulates the full W3 wire protocol for affirmation proofs:
///   1. Host saves request to disk.
///   2. Device loads request, creates response and saves it.
///   3. Host loads response, creates final proof and saves it.
fn run_affirmation_split_protocol<F, P>(
    request_file: &str,
    response_file: &str,
    proof_file: &str,
    device_request: AffirmationDeviceRequest,
    keys: &AccountKeys,
    tree: &AccountProverTree,
    finish: F,
) where
    F: FnOnce(AffirmationDeviceResponse) -> P,
    P: codec::Encode,
{
    // Host
    save_scale_v1(request_file, &device_request);

    // Device
    let req: AffirmationDeviceRequest = load_scale_v1(request_file);
    let device_response = make_affirmation_device_response(keys, &req, tree);
    save_scale_v1(response_file, &device_response);

    // Host
    let res: AffirmationDeviceResponse = load_scale_v1(response_file);
    let proof = finish(res);
    save_scale_v1(proof_file, &proof);
}

pub fn gen_fee_reg_split() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (_, fee_state) = make_fee_state_and_tree(&keys);

    // Host: initialise protocol, send request to device.
    let (protocol, device_request) =
        FeeRegHostProtocol::init(&mut rng, &keys.acct.public, &fee_state, IDENTITY).unwrap();
    save_scale_v1(FEE_REG_SPLIT_REQUEST, &device_request);

    // Device: receive request, create response, send back to host.
    let req: FeeAccountDeviceRequest = load_scale_v1(FEE_REG_SPLIT_REQUEST);
    let device_response = create_fee_account_auth_proof(
        &mut rng,
        &keys.acct,
        &req,
        dart_gens().account_comm_key().sk_gen(),
    )
    .unwrap();
    save_scale_v1(FEE_REG_SPLIT_RESPONSE, &device_response);

    // Host: receive response, finish proof.
    let res: SingleSkDeviceResponse = load_scale_v1(FEE_REG_SPLIT_RESPONSE);
    let proof = protocol.finish::<()>(&res).unwrap();
    save_scale_v1(FEE_REG_SPLIT_PROOF, &proof);
}

#[test]
fn verify_v1_fee_reg_split() {
    let proof: FeeAccountRegistrationProof = load_scale_v1(FEE_REG_SPLIT_PROOF);
    proof.verify(IDENTITY).unwrap();
}

pub fn gen_fee_topup_split() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (tree, mut fee_state) = make_fee_state_and_tree(&keys);

    let (protocol, device_request) = FeeTopupHostProtocol::<FeeAccountTreeConfig>::init(
        &mut rng,
        &keys.acct.public,
        &mut fee_state,
        TOPUP_AMOUNT,
        IDENTITY,
        &tree,
    )
    .unwrap();
    save_scale_v1(FEE_TOPUP_SPLIT_REQUEST, &device_request);

    let req: FeeAccountDeviceRequest = load_scale_v1(FEE_TOPUP_SPLIT_REQUEST);
    let device_response = create_fee_account_auth_proof(
        &mut rng,
        &keys.acct,
        &req,
        dart_gens().account_comm_key().sk_gen(),
    )
    .unwrap();
    save_scale_v1(FEE_TOPUP_SPLIT_RESPONSE, &device_response);

    let res: SingleSkDeviceResponse = load_scale_v1(FEE_TOPUP_SPLIT_RESPONSE);
    let proof = protocol
        .finish::<_, ()>(&mut rng, &res, FeeAccountTreeConfig::parameters())
        .unwrap();
    save_scale_v1(FEE_TOPUP_SPLIT_PROOF, &proof);
}

#[test]
fn verify_v1_fee_topup_split() {
    let keys = alice_keys();
    let (tree, _) = make_fee_state_and_tree(&keys);
    let proof: FeeAccountTopupProof = load_scale_v1(FEE_TOPUP_SPLIT_PROOF);
    let root = tree.root().unwrap().root_node().unwrap();
    proof.verify(&mut default_rng(), IDENTITY, &root).unwrap();
}

pub fn gen_fee_payment_split() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (tree, mut fee_state) = make_fee_state_and_tree_after_topup(&keys);
    let gens = dart_gens();
    let tree_params = FeeAccountTreeConfig::parameters();
    let comm_re_rand_gen = tree_params.even_parameters.sl_params.pc_gens().B_blinding;

    let (protocol, device_request) = FeePaymentHostProtocol::<FeeAccountTreeConfig>::init(
        &mut rng,
        &mut fee_state,
        PAYMENT_AMOUNT,
        IDENTITY,
        &tree,
    )
    .unwrap();
    save_scale_v1(FEE_PAYMENT_SPLIT_REQUEST, &device_request);

    let req: FeePaymentDeviceRequest = load_scale_v1(FEE_PAYMENT_SPLIT_REQUEST);
    let device_response = create_fee_payment_auth_proof(
        &mut rng,
        &keys.acct,
        &req,
        gens.account_comm_key().sk_gen(),
        gens.account_comm_key().randomness_gen(),
        comm_re_rand_gen,
    )
    .unwrap();
    save_scale_v1(FEE_PAYMENT_SPLIT_RESPONSE, &device_response);

    let res: FeePaymentDeviceResponse = load_scale_v1(FEE_PAYMENT_SPLIT_RESPONSE);
    let root_block = tree.get_block_number().unwrap();
    let proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &res,
            root_block,
            FeeAccountTreeConfig::parameters(),
        )
        .unwrap();
    save_scale_v1(FEE_PAYMENT_SPLIT_PROOF, &proof);
}

#[test]
fn verify_v1_fee_payment_split() {
    let keys = alice_keys();
    let (tree, _) = make_fee_state_and_tree_after_topup(&keys);
    let proof: FeeAccountPaymentProof = load_scale_v1(FEE_PAYMENT_SPLIT_PROOF);
    proof
        .verify(&mut default_rng(), IDENTITY, tree.root().unwrap())
        .unwrap();
}

pub fn gen_account_reg_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let keys = alice_keys();
    let (account_state, rho_randomness) = keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    let gens = dart_gens();

    let (protocol, device_request) =
        AccountRegHostProtocol::init(&mut rng, &account_state, rho_randomness, counter, IDENTITY)
            .unwrap();
    save_scale_v1(ACCOUNT_REG_SPLIT_REQUEST, &device_request);

    let req: RegistrationDeviceRequest = load_scale_v1(ACCOUNT_REG_SPLIT_REQUEST);
    let device_response = create_registration_auth_proof(
        &mut rng,
        &keys,
        &req,
        gens.account_comm_key().sk_gen(),
        gens.account_comm_key().sk_enc_gen(),
    )
    .unwrap();
    save_scale_v1(ACCOUNT_REG_SPLIT_RESPONSE, &device_response);

    let res: TwoSksDeviceResponse = load_scale_v1(ACCOUNT_REG_SPLIT_RESPONSE);
    let proof = protocol
        .finish::<_, ()>(&mut rng, &res, counter, AccountTreeConfig::parameters())
        .unwrap();
    save_scale_v1(ACCOUNT_REG_SPLIT_PROOF, &proof);
}

#[test]
fn verify_v1_account_reg_split() {
    let mut rng = default_rng();
    let proof: AccountAssetRegistrationProof = load_scale_v1(ACCOUNT_REG_SPLIT_PROOF);
    proof
        .verify(IDENTITY, AccountTreeConfig::parameters(), &mut rng)
        .unwrap();
}

pub fn gen_mint_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let keys = alice_keys();
    let pk = keys.public_keys();
    let (mut account_state, _) = keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    let tree = make_account_tree(account_state.current_commitment().unwrap());
    let gens = dart_gens();

    let (protocol, device_request) = MintHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &pk,
        &mut account_state,
        MINT_AMOUNT,
        IDENTITY,
        &tree,
    )
    .unwrap();
    save_scale_v1(MINT_SPLIT_REQUEST, &device_request);

    let req: RegistrationDeviceRequest = load_scale_v1(MINT_SPLIT_REQUEST);
    let device_response = create_registration_auth_proof(
        &mut rng,
        &keys,
        &req,
        gens.account_comm_key().sk_gen(),
        gens.account_comm_key().sk_enc_gen(),
    )
    .unwrap();
    save_scale_v1(MINT_SPLIT_RESPONSE, &device_response);

    let res: TwoSksDeviceResponse = load_scale_v1(MINT_SPLIT_RESPONSE);
    let root_block = tree.get_block_number().unwrap();
    let proof = protocol
        .finish::<_, ()>(&mut rng, &res, root_block, AccountTreeConfig::parameters())
        .unwrap();
    save_scale_v1(MINT_SPLIT_PROOF, &proof);
}

#[test]
fn verify_v1_mint_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let keys = alice_keys();
    let (account_state, _) = keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    let tree = make_account_tree(account_state.current_commitment().unwrap());
    let proof: AssetMintingProof = load_scale_v1(MINT_SPLIT_PROOF);
    proof
        .verify(IDENTITY, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_sender_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.balance = BALANCE;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) = SenderAffirmationHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut sender_state,
        &leg_ref,
        &leg_enc,
        SETTLEMENT_AMOUNT,
        &tree,
    )
    .unwrap();
    assert_eq!(device_request.k_asset_ids.len(), 1);
    run_affirmation_split_protocol(
        SENDER_AFFIRM_SPLIT_REQUEST,
        SENDER_AFFIRM_SPLIT_RESPONSE,
        SENDER_AFFIRM_SPLIT_PROOF,
        device_request,
        &sender_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_sender_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.balance = BALANCE;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let proof: SenderAffirmationProof = load_scale_v1(SENDER_AFFIRM_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_receiver_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) = ReceiverAffirmationHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut receiver_state,
        &leg_ref,
        &leg_enc,
        &tree,
    )
    .unwrap();
    assert_eq!(device_request.k_asset_ids.len(), 1);
    run_affirmation_split_protocol(
        RECEIVER_AFFIRM_SPLIT_REQUEST,
        RECEIVER_AFFIRM_SPLIT_RESPONSE,
        RECEIVER_AFFIRM_SPLIT_PROOF,
        device_request,
        &receiver_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_receiver_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let proof: ReceiverAffirmationProof = load_scale_v1(RECEIVER_AFFIRM_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_receiver_counter_update_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    receiver_state.current_state.counter = 1;
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        0,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) = ReceiverCounterUpdateHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut receiver_state,
        &leg_ref,
        &leg_enc,
        &tree,
    )
    .unwrap();
    run_affirmation_split_protocol(
        RECEIVER_COUNTER_UPDATE_SPLIT_REQUEST,
        RECEIVER_COUNTER_UPDATE_SPLIT_RESPONSE,
        RECEIVER_COUNTER_UPDATE_SPLIT_PROOF,
        device_request,
        &receiver_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_receiver_counter_update_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    receiver_state.current_state.counter = 1;
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        0,
    );
    let tree = make_account_tree(leaf);
    let proof: ReceiverCounterUpdateProof = load_scale_v1(RECEIVER_COUNTER_UPDATE_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_claim_received_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    // Counter must be > 0 so the counter-decrease state transition is valid.
    receiver_state.current_state.counter = 1;
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) = ClaimReceivedHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut receiver_state,
        &leg_ref,
        &leg_enc,
        SETTLEMENT_AMOUNT,
        &tree,
    )
    .unwrap();
    run_affirmation_split_protocol(
        CLAIM_RECEIVED_SPLIT_REQUEST,
        CLAIM_RECEIVED_SPLIT_RESPONSE,
        CLAIM_RECEIVED_SPLIT_PROOF,
        device_request,
        &receiver_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_claim_received_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    receiver_state.current_state.counter = 1;
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let proof: ReceiverClaimProof = load_scale_v1(CLAIM_RECEIVED_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_sender_reverse_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.counter = 1;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) = SenderReverseHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut sender_state,
        &leg_ref,
        &leg_enc,
        SETTLEMENT_AMOUNT,
        &tree,
    )
    .unwrap();
    run_affirmation_split_protocol(
        SENDER_REVERSE_SPLIT_REQUEST,
        SENDER_REVERSE_SPLIT_RESPONSE,
        SENDER_REVERSE_SPLIT_PROOF,
        device_request,
        &sender_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_sender_reverse_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.counter = 1;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let proof: SenderReversalProof = load_scale_v1(SENDER_REVERSE_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_sender_counter_update_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.counter = 1;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        0,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) = SenderCounterUpdateHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut sender_state,
        &leg_ref,
        &leg_enc,
        &tree,
    )
    .unwrap();
    run_affirmation_split_protocol(
        SENDER_COUNTER_UPDATE_SPLIT_REQUEST,
        SENDER_COUNTER_UPDATE_SPLIT_RESPONSE,
        SENDER_COUNTER_UPDATE_SPLIT_PROOF,
        device_request,
        &sender_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_sender_counter_update_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.counter = 1;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        0,
    );
    let tree = make_account_tree(leaf);
    let proof: SenderCounterUpdateProof = load_scale_v1(SENDER_COUNTER_UPDATE_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_instant_sender_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.balance = BALANCE;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) =
        InstantSenderAffirmationHostProtocol::<AccountTreeConfig>::init(
            &mut rng,
            &mut sender_state,
            &leg_ref,
            &leg_enc,
            SETTLEMENT_AMOUNT,
            &tree,
        )
        .unwrap();
    run_affirmation_split_protocol(
        INSTANT_SENDER_AFFIRM_SPLIT_REQUEST,
        INSTANT_SENDER_AFFIRM_SPLIT_RESPONSE,
        INSTANT_SENDER_AFFIRM_SPLIT_PROOF,
        device_request,
        &sender_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_instant_sender_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut sender_state, _) = sender_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    sender_state.current_state.balance = BALANCE;
    let leaf = sender_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let proof: InstantSenderAffirmationProof = load_scale_v1(INSTANT_SENDER_AFFIRM_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}

pub fn gen_instant_receiver_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (mut receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, leg_ref) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let (protocol, device_request) =
        InstantReceiverAffirmationHostProtocol::<AccountTreeConfig>::init(
            &mut rng,
            &mut receiver_state,
            &leg_ref,
            &leg_enc,
            SETTLEMENT_AMOUNT,
            &tree,
        )
        .unwrap();
    run_affirmation_split_protocol(
        INSTANT_RECEIVER_AFFIRM_SPLIT_REQUEST,
        INSTANT_RECEIVER_AFFIRM_SPLIT_RESPONSE,
        INSTANT_RECEIVER_AFFIRM_SPLIT_PROOF,
        device_request,
        &receiver_keys,
        &tree,
        |res| protocol.finish::<_, ()>(&mut rng, &res).unwrap(),
    );
}

#[test]
fn verify_v1_instant_receiver_affirm_split() {
    let mut rng = default_rng();
    let counter: NullifierSkGenCounter = 0;
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let (receiver_state, _) = receiver_keys
        .init_asset_state(ASSET_ID_1, counter, IDENTITY)
        .unwrap();
    let leaf = receiver_state.current_commitment().unwrap();
    let (leg_enc, _) = make_hidden_asset_leg_enc(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_1,
        SETTLEMENT_AMOUNT,
    );
    let tree = make_account_tree(leaf);
    let proof: InstantReceiverAffirmationProof = load_scale_v1(INSTANT_RECEIVER_AFFIRM_SPLIT_PROOF);
    proof
        .verify(&leg_enc, tree.root().unwrap(), &mut rng)
        .unwrap();
}
