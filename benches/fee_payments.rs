use criterion::{Criterion, criterion_group, criterion_main};
use rand::SeedableRng;
use std::hint::black_box;

use polymesh_dart::{curve_tree::*, *};

fn fee_proof_benchmark(c: &mut Criterion) {
    let mut rng = rand_chacha::ChaCha20Rng::from_seed([42; 32]);
    let ctx = b"fee_benchmark";

    // Set up fee account tree (assuming FeeAccountCurveTree exists; adjust if needed).
    let mut fee_account_tree =
        ProverCurveTree::<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>::new(
            FEE_ACCOUNT_TREE_HEIGHT,
        )
        .expect("Failed to create fee account tree");

    // Generate account keys.
    let account_keys = AccountKeys::rand(&mut rng).expect("Failed to generate account keys");
    let asset_id = 0 as AssetId;
    let initial_balance = 1000u64;
    let topup_amount = 500u64;
    let payment_amount = 200u64;

    // Benchmark: Generate FeeAccountRegistrationProof.
    c.bench_function("FeeAccountRegistrationProof generate", |b| {
        b.iter(|| {
            let (_proof, _account_state) = FeeAccountRegistrationProof::new(
                &mut rng,
                black_box(&account_keys.acct),
                asset_id,
                initial_balance,
                ctx,
            )
            .expect("Failed to generate registration proof");
        })
    });

    // Generate a registration proof for verification benchmark.
    let (reg_proof, mut fee_account_state) = FeeAccountRegistrationProof::new(
        &mut rng,
        &account_keys.acct,
        asset_id,
        initial_balance,
        ctx,
    )
    .expect("Failed to generate registration proof");
    fee_account_state
        .commit_pending_state()
        .expect("Failed to commit pending state");
    let current_commitment = fee_account_state
        .current_commitment(&account_keys.acct)
        .expect("Failed to get current commitment");
    let leaf = current_commitment
        .as_leaf_value()
        .expect("Failed to get leaf value");
    fee_account_tree
        .insert(leaf)
        .expect("Failed to insert into fee account tree");

    // Benchmark: Verify FeeAccountRegistrationProof.
    c.bench_function("FeeAccountRegistrationProof verify", |b| {
        b.iter(|| {
            reg_proof
                .verify(black_box(ctx))
                .expect("Failed to verify registration proof");
        })
    });

    // Update tree root after registration.
    let fee_account_root = fee_account_tree
        .root()
        .expect("Failed to get fee account tree root");

    // Benchmark: Generate FeeAccountTopupProof.
    c.bench_function("FeeAccountTopupProof generate", |b| {
        b.iter(|| {
            let _proof = FeeAccountTopupProof::new(
                &mut rng,
                black_box(&account_keys.acct),
                &mut fee_account_state.clone(),
                topup_amount,
                ctx,
                &fee_account_tree,
            )
            .expect("Failed to generate topup proof");
        })
    });

    // Generate a topup proof for verification benchmark.
    let topup_proof = FeeAccountTopupProof::new(
        &mut rng,
        &account_keys.acct,
        &mut fee_account_state,
        topup_amount,
        ctx,
        &fee_account_tree,
    )
    .expect("Failed to generate topup proof");
    fee_account_state
        .commit_pending_state()
        .expect("Failed to commit pending state");
    fee_account_tree
        .insert(
            topup_proof
                .updated_account_state_commitment
                .as_leaf_value()
                .expect("Failed to get leaf value"),
        )
        .expect("Failed to insert updated state into fee account tree");

    // Benchmark: Verify FeeAccountTopupProof.
    c.bench_function("FeeAccountTopupProof verify", |b| {
        b.iter(|| {
            topup_proof
                .verify(&mut rng, black_box(ctx), &fee_account_root)
                .expect("Failed to verify topup proof");
        })
    });

    // Update tree root after topup.
    let fee_account_root = fee_account_tree
        .root()
        .expect("Failed to get updated fee account tree root");

    // Benchmark: Generate FeeAccountPaymentProof.
    c.bench_function("FeeAccountPaymentProof generate", |b| {
        b.iter(|| {
            let _proof = FeeAccountPaymentProof::new(
                &mut rng,
                black_box(&account_keys.acct),
                ctx,
                &mut fee_account_state.clone(),
                payment_amount,
                &fee_account_tree,
            )
            .expect("Failed to generate payment proof");
        })
    });

    // Generate a payment proof for verification benchmark.
    let payment_proof = FeeAccountPaymentProof::new(
        &mut rng,
        &account_keys.acct,
        ctx,
        &mut fee_account_state,
        payment_amount,
        &fee_account_tree,
    )
    .expect("Failed to generate payment proof");

    // Benchmark: Verify FeeAccountPaymentProof.
    c.bench_function("FeeAccountPaymentProof verify", |b| {
        b.iter(|| {
            payment_proof
                .verify(&mut rng, black_box(ctx), &fee_account_root)
                .expect("Failed to verify payment proof");
        })
    });
}

criterion_group!(fee_proof_benches, fee_proof_benchmark);
criterion_main!(fee_proof_benches);
