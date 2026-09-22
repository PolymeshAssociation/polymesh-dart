//! The current `dart-bp/docs/6.md` fee mechanism, measured on this machine so the comparison with
//! BAT is like for like rather than against numbers from another run.
//!
//! Sizes are SCALE, which is what goes on chain. Payment is the proof BAT's spend replaces and
//! top-up is what BAT's issuance replaces. Registration is run to produce the account state the
//! other two build on, and is not measured: it has no BAT counterpart, since tokens are bearer
//! objects and a fee account is never created.

use crate::measure::bench;
use codec::Encode;
use polymesh_dart::{curve_tree::*, *};
use rand::SeedableRng;
use std::time::Duration;

pub struct Row {
    pub prove: Duration,
    pub verify: Duration,
    pub size: usize,
}

pub struct Baseline {
    pub topup: Row,
    pub payment: Row,
}

pub fn measure(iters: usize, payment_amount: u64) -> Baseline {
    let mut rng = rand_chacha::ChaCha20Rng::from_seed([42; 32]);
    let ctx = b"bat-poc-baseline";

    let mut tree =
        ProverCurveTree::<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>::new(
            FEE_ACCOUNT_TREE_HEIGHT,
        )
        .expect("fee account tree");

    let account_keys = AccountKeys::rand(&mut rng).expect("account keys");
    let asset_id = 0 as AssetId;
    let initial_balance = 1_000_000u64;
    let topup_amount = 500_000u64;

    let (_, mut state) = FeeAccountRegistrationProof::<()>::new(
        &mut rng,
        &account_keys.acct,
        asset_id,
        initial_balance,
        ctx,
    )
    .expect("registration proof");

    state.commit_pending_state().expect("commit");
    tree.insert(
        state
            .current_commitment()
            .expect("commitment")
            .as_leaf_value()
            .expect("leaf"),
    )
    .expect("insert");
    let root = tree.root().expect("root").root_node().expect("root node");

    let t_topup_prove = bench(iters, || {
        FeeAccountTopupProof::<()>::new(
            &mut rng,
            &account_keys.acct,
            &mut state.clone(),
            topup_amount,
            ctx,
            &tree,
        )
        .expect("topup proof")
    });
    let topup_proof = FeeAccountTopupProof::<()>::new(
        &mut rng,
        &account_keys.acct,
        &mut state,
        topup_amount,
        ctx,
        &tree,
    )
    .expect("topup proof");
    let t_topup_verify = bench(iters, || {
        topup_proof
            .verify(&mut rng, ctx, &root)
            .expect("verify topup")
    });
    let topup_size = topup_proof.encode().len();

    state.commit_pending_state().expect("commit");
    tree.insert(
        topup_proof
            .updated_account_state_commitment
            .as_leaf_value()
            .expect("leaf"),
    )
    .expect("insert");
    let root = tree.root().expect("root");

    let t_pay_prove = bench(iters, || {
        FeeAccountPaymentProof::<()>::new(
            &mut rng,
            &account_keys.acct,
            ctx,
            &mut state.clone(),
            payment_amount,
            &tree,
        )
        .expect("payment proof")
    });
    let pay_proof = FeeAccountPaymentProof::<()>::new(
        &mut rng,
        &account_keys.acct,
        ctx,
        &mut state,
        payment_amount,
        &tree,
    )
    .expect("payment proof");
    let t_pay_verify = bench(iters, || {
        pay_proof
            .verify(&mut rng, ctx, &root)
            .expect("verify payment")
    });
    let pay_size = pay_proof.encode().len();

    Baseline {
        topup: Row {
            prove: t_topup_prove,
            verify: t_topup_verify,
            size: topup_size,
        },
        payment: Row {
            prove: t_pay_prove,
            verify: t_pay_verify,
            size: pay_size,
        },
    }
}
