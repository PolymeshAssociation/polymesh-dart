use polymesh_dart::curve_tree::{AccountTreeConfig, CurveTreeConfig, ProverCurveTree};
use polymesh_dart::key_distribution_proof::KeyDistributionProof;
use polymesh_dart::*;

use crate::constants::*;
use crate::utils::{
    alice_keys, default_rng, load_canonical_v1, load_scale_v1, save_canonical_v1, save_scale_v1,
};

const BATCH_PROOF_SEEDS: [&str; 5] = [ALICE_SEED, BOB_SEED, CAROL_SEED, DAVE_SEED, EVE_SEED];

fn batched_fee_account_registration_proof_file() -> String {
    format!(
        "{}_{}.bin",
        BATCHED_FEE_ACCOUNT_REGISTRATION_PROOF, FEE_REG_BATCH_SIZE
    )
}

fn batched_account_asset_registration_proof_file() -> String {
    format!(
        "{}_{}.bin",
        BATCHED_ACCOUNT_ASSET_REGISTRATION_PROOF, ASSET_BATCH_SIZE
    )
}

fn asset_commitment_data_file(n_enc: usize, n_med: usize) -> String {
    format!(
        "{}_enc_{}_med_{}.bin",
        ASSET_COMMITMENT_DATA_PREFIX, n_enc, n_med
    )
}

fn key_distribution_proof_file(n_recipients: usize) -> String {
    format!(
        "{}_{}_recipients.bin",
        KEY_DISTRIBUTION_PROOF_PREFIX, n_recipients
    )
}

pub fn gen_plain_objects() {
    let mut rng = default_rng();
    let keys = alice_keys();

    save_scale_v1(ACCOUNT_KEYS, &keys);
    save_scale_v1(ACCOUNT_KEY_PAIR, &keys.acct);
    save_scale_v1(ENCRYPTION_KEY_PAIR, &keys.enc);
    save_scale_v1(ACCOUNT_PUBLIC_KEYS, &keys.public_keys());

    let (account_asset_state, _) =
        AccountAssetState::new(&keys, ASSET_ID_1, 0u16, IDENTITY).unwrap();
    let current_state = &account_asset_state.current_state;
    let commitment = current_state.commitment().unwrap();
    let nullifier = current_state.nullifier().unwrap();

    save_scale_v1(ACCOUNT_STATE, current_state);
    save_scale_v1(ACCOUNT_STATE_COMMITMENT, &commitment);
    save_scale_v1(ACCOUNT_STATE_NULLIFIER, &nullifier);

    // pending_state = None
    save_scale_v1(ACCOUNT_ASSET_STATE_NO_PENDING, &account_asset_state);

    // pending_state = Some
    let mut with_pending = account_asset_state;
    with_pending.mint(MINT_AMOUNT).unwrap();
    save_scale_v1(ACCOUNT_ASSET_STATE_WITH_PENDING, &with_pending);

    // AssetCommitmentData with 1 auditor, 1 mediator
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    let asset_commitment_data = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors)
        .unwrap()
        .asset_data()
        .unwrap();
    save_canonical_v1(&asset_commitment_data_file(1, 1), &asset_commitment_data);
    save_canonical_v1(
        ASSET_COMMITMENT_PARAMETERS,
        curve_tree::get_asset_commitment_parameters(),
    );
    save_canonical_v1(DART_BP_GENERATORS, dart_gens());
}

#[test]
fn verify_v1_scale_plain_objects() {
    let expected_keys = alice_keys();

    let loaded: AccountKeys = load_scale_v1(ACCOUNT_KEYS);
    assert_eq!(loaded, expected_keys);

    let loaded: AccountKeyPair = load_scale_v1(ACCOUNT_KEY_PAIR);
    assert_eq!(loaded, expected_keys.acct);

    let loaded: EncryptionKeyPair = load_scale_v1(ENCRYPTION_KEY_PAIR);
    assert_eq!(loaded, expected_keys.enc);

    let loaded: AccountPublicKeys = load_scale_v1(ACCOUNT_PUBLIC_KEYS);
    assert_eq!(loaded, expected_keys.public_keys());

    let (expected_asset_state, _) =
        AccountAssetState::new(&expected_keys, ASSET_ID_1, 0u16, IDENTITY).unwrap();
    let expected_state = &expected_asset_state.current_state;

    let loaded: AccountState = load_scale_v1(ACCOUNT_STATE);
    assert_eq!(loaded, *expected_state);

    let loaded: AccountStateCommitment = load_scale_v1(ACCOUNT_STATE_COMMITMENT);
    assert_eq!(loaded, expected_state.commitment().unwrap());

    let loaded: AccountStateNullifier = load_scale_v1(ACCOUNT_STATE_NULLIFIER);
    assert_eq!(loaded, expected_state.nullifier().unwrap());

    // AccountAssetState: no pending
    let loaded: AccountAssetState = load_scale_v1(ACCOUNT_ASSET_STATE_NO_PENDING);
    assert_eq!(loaded.current_state, expected_asset_state.current_state);
    assert!(loaded.pending_state.is_none());

    // AccountAssetState: with pending
    let mut expected_with_pending = expected_asset_state;
    expected_with_pending.mint(MINT_AMOUNT).unwrap();
    let loaded: AccountAssetState = load_scale_v1(ACCOUNT_ASSET_STATE_WITH_PENDING);
    assert_eq!(loaded.current_state, expected_with_pending.current_state);
    assert_eq!(
        loaded.pending_state.as_ref().unwrap(),
        expected_with_pending.pending_state.as_ref().unwrap(),
    );

    let _: AssetCommitmentData = load_canonical_v1(&asset_commitment_data_file(1, 1));
    let _: curve_tree::AssetCommitmentParameters<curve_tree::AssetTreeConfig> =
        load_canonical_v1(ASSET_COMMITMENT_PARAMETERS);
    let loaded: DartBPGenerators = load_canonical_v1(DART_BP_GENERATORS);
    assert_eq!(loaded, dart_gens().clone());
}

pub fn gen_account_registration_proof() {
    let mut rng = default_rng();
    let account_keys = alice_keys();
    let proof = AccountRegistrationProof::<()>::new(&mut rng, &[account_keys], IDENTITY).unwrap();
    save_scale_v1(ACCOUNT_REGISTRATION_PROOF, &proof);
}

pub fn gen_encryption_key_registration_proof() {
    let mut rng = default_rng();
    let enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let proof = EncryptionKeyRegistrationProof::<()>::new(&mut rng, &[enc_key], IDENTITY).unwrap();
    save_scale_v1(ENCRYPTION_KEY_REGISTRATION_PROOF, &proof);
}

pub fn gen_fee_account_registration_proof() {
    let mut rng = default_rng();
    let fee_keys = alice_keys();
    let (proof, _) = FeeAccountRegistrationProof::<()>::new(
        &mut rng,
        &fee_keys.acct,
        ASSET_ID_1,
        BALANCE,
        IDENTITY,
    )
    .unwrap();
    save_scale_v1(FEE_ACCOUNT_REGISTRATION_PROOF, &proof);
}

pub fn gen_account_asset_registration_proof() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let asset_reg_keys = alice_keys();
    let (proof, _) = AccountAssetRegistrationProof::<()>::new(
        &mut rng,
        &asset_reg_keys,
        ASSET_ID_1,
        0u16,
        IDENTITY,
        tree_params,
    )
    .unwrap();
    save_scale_v1(ACCOUNT_ASSET_REGISTRATION_PROOF, &proof);
}

pub fn gen_batched_fee_account_registration_proof() {
    let mut rng = default_rng();
    let seeds = BATCH_PROOF_SEEDS
        .get(..FEE_REG_BATCH_SIZE)
        .expect("FEE_REG_BATCH_SIZE exceeds number of configured test seeds");
    let keys: Vec<AccountKeys> = seeds
        .iter()
        .map(|s| AccountKeys::from_seed(s).unwrap())
        .collect();
    let registrations: Vec<(&AccountKeyPair, AssetId, Balance)> = keys
        .iter()
        .enumerate()
        .map(|(i, k)| {
            (
                &k.acct,
                ASSET_ID_1 + i as AssetId,
                BALANCE * (i as Balance + 1),
            )
        })
        .collect();
    let (proof, _) =
        BatchedFeeAccountRegistrationProof::<()>::new(&mut rng, &registrations, IDENTITY).unwrap();
    let filename = batched_fee_account_registration_proof_file();
    save_scale_v1(&filename, &proof);
}

pub fn gen_batched_account_asset_registration_proof() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let seeds = BATCH_PROOF_SEEDS
        .get(..ASSET_BATCH_SIZE)
        .expect("ASSET_BATCH_SIZE exceeds number of configured test seeds");
    let keys: Vec<AccountKeys> = seeds
        .iter()
        .map(|s| AccountKeys::from_seed(s).unwrap())
        .collect();
    let account_assets: Vec<(AccountKeys, AssetId, u16)> = keys
        .into_iter()
        .enumerate()
        .map(|(i, k)| (k, ASSET_ID_1 + i as AssetId, 0u16))
        .collect();
    let (proof, _) = BatchedAccountAssetRegistrationProof::<()>::new(
        &mut rng,
        &account_assets,
        IDENTITY,
        tree_params,
    )
    .unwrap();
    let filename = batched_account_asset_registration_proof_file();
    save_scale_v1(&filename, &proof);
}

pub fn gen_key_distribution_proof_2_recipients() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let dist_keys = alice_keys();
    let recipient_pks: Vec<EncryptionPublicKey> = [ALICE_SEED, BOB_SEED]
        .iter()
        .map(|s| AccountKeys::from_seed(s).unwrap().enc.public)
        .collect();
    let proof = KeyDistributionProof::<()>::new(
        &mut rng,
        dist_keys.enc.secret.clone(),
        &dist_keys.enc.public,
        &recipient_pks,
        NONCE,
        tree_params,
    )
    .unwrap();
    save_scale_v1(&key_distribution_proof_file(2), &proof);
}

pub fn gen_key_distribution_proof_3_recipients() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let dist_keys = alice_keys();
    let recipient_pks: Vec<EncryptionPublicKey> = [ALICE_SEED, BOB_SEED, CAROL_SEED]
        .iter()
        .map(|s| AccountKeys::from_seed(s).unwrap().enc.public)
        .collect();
    let proof = KeyDistributionProof::<()>::new(
        &mut rng,
        dist_keys.enc.secret.clone(),
        &dist_keys.enc.public,
        &recipient_pks,
        NONCE,
        tree_params,
    )
    .unwrap();
    save_scale_v1(&key_distribution_proof_file(3), &proof);
}

pub fn gen_asset_minting_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (mut asset_state, _) = AccountAssetState::new(&keys, ASSET_ID_1, 0u16, IDENTITY).unwrap();
    let account_tree = alice_account_tree(&keys);
    let proof = AssetMintingProof::<()>::new(
        &mut rng,
        &keys,
        IDENTITY,
        &mut asset_state,
        &account_tree,
        MINT_AMOUNT,
    )
    .unwrap();
    save_scale_v1(ASSET_MINTING_PROOF, &proof);
}

pub fn alice_account_tree(
    keys: &AccountKeys,
) -> ProverCurveTree<{ ACCOUNT_TREE_L }, { ACCOUNT_TREE_M }, AccountTreeConfig> {
    let (asset_state, _) = AccountAssetState::new(keys, ASSET_ID_1, 0u16, IDENTITY).unwrap();
    let mut tree = ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
        ACCOUNT_TREE_HEIGHT,
    )
    .unwrap();
    let leaf = asset_state
        .current_commitment()
        .unwrap()
        .as_leaf_value()
        .unwrap();
    tree.insert(leaf).unwrap();
    tree.store_root().unwrap();
    tree
}

#[test]
fn verify_v1_account_registration_proof() {
    let proof: AccountRegistrationProof = load_scale_v1(ACCOUNT_REGISTRATION_PROOF);
    proof.verify(IDENTITY).unwrap();
}

#[test]
fn verify_v1_encryption_key_registration_proof() {
    let proof: EncryptionKeyRegistrationProof = load_scale_v1(ENCRYPTION_KEY_REGISTRATION_PROOF);
    proof.verify(IDENTITY).unwrap();
}

#[test]
fn verify_v1_fee_account_registration_proof() {
    let proof: FeeAccountRegistrationProof = load_scale_v1(FEE_ACCOUNT_REGISTRATION_PROOF);
    proof.verify(IDENTITY).unwrap();
}

#[test]
fn verify_v1_batched_fee_account_registration_proof() {
    let filename = batched_fee_account_registration_proof_file();
    let proof: BatchedFeeAccountRegistrationProof = load_scale_v1(&filename);
    assert_eq!(proof.proofs.len(), FEE_REG_BATCH_SIZE);
    proof.verify(IDENTITY).unwrap();
}

#[test]
fn verify_v1_account_asset_registration_proof() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let proof: AccountAssetRegistrationProof = load_scale_v1(ACCOUNT_ASSET_REGISTRATION_PROOF);
    proof.verify(IDENTITY, tree_params, &mut rng).unwrap();
}

#[test]
fn verify_v1_batched_account_asset_registration_proof() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let filename = batched_account_asset_registration_proof_file();
    let proof: BatchedAccountAssetRegistrationProof = load_scale_v1(&filename);
    assert_eq!(proof.proofs.len(), ASSET_BATCH_SIZE);
    proof.verify(IDENTITY, tree_params, &mut rng).unwrap();
}

#[test]
fn verify_v1_key_distribution_proof_2_recipients() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let proof: KeyDistributionProof = load_scale_v1(&key_distribution_proof_file(2));
    proof.verify(NONCE, tree_params, &mut rng).unwrap();
}

#[test]
fn verify_v1_key_distribution_proof_3_recipients() {
    let mut rng = default_rng();
    let tree_params = AccountTreeConfig::parameters();
    let proof: KeyDistributionProof = load_scale_v1(&key_distribution_proof_file(3));
    proof.verify(NONCE, tree_params, &mut rng).unwrap();
}

#[test]
fn verify_v1_asset_minting_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let account_tree = alice_account_tree(&keys);
    let proof: AssetMintingProof = load_scale_v1(ASSET_MINTING_PROOF);
    proof
        .verify(IDENTITY, account_tree.root().unwrap(), &mut rng)
        .unwrap();
}
