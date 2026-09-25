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

pub fn gen_batched_fee_account_topup_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (fee_tree, fee_state) = alice_fee_tree(&keys);
    let mut topups = vec![(&keys.acct, TOPUP_AMOUNT, fee_state)];
    let proof =
        BatchedFeeAccountTopupProof::<()>::new(&mut rng, &mut topups, IDENTITY, &fee_tree).unwrap();
    save_scale_v1(BATCHED_FEE_ACCOUNT_TOPUP_PROOF, &proof);
}

pub fn gen_fee_account_topup_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (fee_tree, mut fee_state) = alice_fee_tree(&keys);
    let proof = FeeAccountTopupProof::<()>::new(
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
    let topup_proof = FeeAccountTopupProof::<()>::new(
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
    let proof = FeeAccountPaymentProof::<()>::new(
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

pub fn gen_fee_payment_with_batched_proofs() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (fee_tree, mut fee_state) = fee_tree_and_state_after_topup(&keys);
    let proof = FeePaymentWithBatchedProofs::<()>::new(
        &mut rng,
        &keys.acct,
        BatchedProofs::new(),
        &mut fee_state,
        Some(IDENTITY),
        PAYMENT_AMOUNT,
        fee_tree,
    )
    .unwrap();
    save_scale_v1(FEE_PAYMENT_WITH_BATCHED_PROOFS, &proof);
}

pub fn gen_fee_payment_with_batched_proofs_broadcast() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (fee_tree, mut fee_state) = fee_tree_and_state_after_topup(&keys);
    let proof = FeePaymentWithBatchedProofs::<()>::new(
        &mut rng,
        &keys.acct,
        BatchedProofs::new(),
        &mut fee_state,
        None,
        PAYMENT_AMOUNT,
        fee_tree,
    )
    .unwrap();
    save_scale_v1(FEE_PAYMENT_WITH_BATCHED_PROOFS_BROADCAST, &proof);
}

fn fee_tree_and_state_after_topup(keys: &AccountKeys) -> (FeeProverTree, FeeAccountAssetState) {
    let mut rng = default_rng();
    let (mut fee_tree, mut fee_state) = alice_fee_tree(keys);
    let topup_proof = FeeAccountTopupProof::<()>::new(
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
    (fee_tree, fee_state)
}

fn fee_tree_after_topup(keys: &AccountKeys) -> FeeProverTree {
    fee_tree_and_state_after_topup(keys).0
}

#[test]
fn verify_v1_fee_account_topup_proof() {
    let mut rng = default_rng();
    let keys = alice_keys();
    let (fee_tree, _) = alice_fee_tree(&keys);
    let proof: FeeAccountTopupProof = load_scale_v1(FEE_ACCOUNT_TOPUP_PROOF);
    let root = fee_tree.root().unwrap();
    proof.verify(&mut rng, IDENTITY, &root).unwrap();
}

#[test]
fn verify_v1_batched_fee_account_topup_proof() {
    let keys = alice_keys();
    let (fee_tree, _) = alice_fee_tree(&keys);
    let proof: BatchedFeeAccountTopupProof = load_scale_v1(BATCHED_FEE_ACCOUNT_TOPUP_PROOF);
    assert_eq!(proof.len(), 1);
    let root = fee_tree.root().unwrap();
    proof.verify(&mut default_rng(), IDENTITY, &root).unwrap();
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

#[test]
fn verify_v1_fee_payment_with_batched_proofs() {
    let keys = alice_keys();
    let fee_tree = fee_tree_after_topup(&keys);
    let root = fee_tree.root().unwrap();
    let proof: FeePaymentWithBatchedProofs = load_scale_v1(FEE_PAYMENT_WITH_BATCHED_PROOFS);
    assert!(!proof.is_broadcast);
    proof
        .verify_fee_payment(&mut default_rng(), Some(IDENTITY), root)
        .unwrap();
}

#[test]
fn verify_v1_fee_payment_with_batched_proofs_broadcast() {
    let keys = alice_keys();
    let fee_tree = fee_tree_after_topup(&keys);
    let root = fee_tree.root().unwrap();
    let proof: FeePaymentWithBatchedProofs =
        load_scale_v1(FEE_PAYMENT_WITH_BATCHED_PROOFS_BROADCAST);
    assert!(proof.is_broadcast);
    proof
        .verify_fee_payment(&mut default_rng(), None, root)
        .unwrap();
}
