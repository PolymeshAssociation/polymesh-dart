use polymesh_dart::curve_tree::{FeeAccountTreeConfig, ProverCurveTree};
use polymesh_dart::*;

use crate::constants::*;
use crate::utils::{alice_keys, default_rng, load_scale_v1, save_scale_v1};

type FeeProverTree = ProverCurveTree<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>;

fn alice_fee_tree(keys: &AccountKeys) -> (FeeProverTree, FeeAccountAssetState) {
    let mut rng = default_rng();
    let fee_state =
        FeeAccountAssetState::new(&mut rng, &keys.acct.public, ASSET_ID_1, BALANCE).unwrap();
    let mut fee_tree = FeeProverTree::new(FEE_ACCOUNT_TREE_HEIGHT).unwrap();
    let leaf = fee_state
        .current_commitment()
        .unwrap()
        .as_leaf_value()
        .unwrap();
    fee_tree.insert(leaf).unwrap();
    fee_tree.store_root().unwrap();
    (fee_tree, fee_state)
}

pub fn gen_fee_account_topup_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (fee_tree, mut fee_state) = alice_fee_tree(&keys);
    let proof = FeeAccountTopupProof::new(
        &mut rng,
        &keys.acct,
        &mut fee_state,
        TOPUP_AMOUNT,
        IDENTITY,
        &fee_tree,
    )
    .unwrap();
    save_scale_v1(FEE_ACCOUNT_TOPUP_PROOF, &proof);
}

pub fn gen_fee_account_payment_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (mut fee_tree, mut fee_state) = alice_fee_tree(&keys);
    let topup_proof = FeeAccountTopupProof::new(
        &mut rng,
        &keys.acct,
        &mut fee_state,
        TOPUP_AMOUNT,
        IDENTITY,
        &fee_tree,
    )
    .unwrap();
    fee_state.commit_pending_state().unwrap();
    let updated_leaf = topup_proof
        .updated_account_state_commitment
        .as_leaf_value()
        .unwrap();
    fee_tree.insert(updated_leaf).unwrap();
    fee_tree.store_root().unwrap();
    let proof = FeeAccountPaymentProof::new(
        &mut rng,
        &keys.acct,
        IDENTITY,
        &mut fee_state,
        PAYMENT_AMOUNT,
        &fee_tree,
    )
    .unwrap();
    save_scale_v1(FEE_ACCOUNT_PAYMENT_PROOF, &proof);
}

fn fee_tree_after_topup(keys: &AccountKeys) -> FeeProverTree {
    let mut rng = default_rng();
    let (mut fee_tree, mut fee_state) = alice_fee_tree(keys);
    let topup_proof = FeeAccountTopupProof::new(
        &mut rng,
        &keys.acct,
        &mut fee_state,
        TOPUP_AMOUNT,
        IDENTITY,
        &fee_tree,
    )
    .unwrap();
    fee_state.commit_pending_state().unwrap();
    let updated_leaf = topup_proof
        .updated_account_state_commitment
        .as_leaf_value()
        .unwrap();
    fee_tree.insert(updated_leaf).unwrap();
    fee_tree.store_root().unwrap();
    fee_tree
}

#[test]
fn verify_v1_fee_account_topup_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (fee_tree, _) = alice_fee_tree(&keys);
    let proof: FeeAccountTopupProof = load_scale_v1(FEE_ACCOUNT_TOPUP_PROOF);
    let root = fee_tree.root().unwrap().root_node().unwrap();
    proof.verify(&mut rng, IDENTITY, &root).unwrap();
}

#[test]
fn verify_v1_fee_account_payment_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let fee_tree = fee_tree_after_topup(&keys);
    let proof: FeeAccountPaymentProof = load_scale_v1(FEE_ACCOUNT_PAYMENT_PROOF);
    proof
        .verify(&mut rng, IDENTITY, fee_tree.root().unwrap())
        .unwrap();
}
