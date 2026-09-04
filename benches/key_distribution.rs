use criterion::{Criterion, criterion_group, criterion_main};
use rand::SeedableRng;
use std::hint::black_box;

use polymesh_dart::key_distribution_proof::KeyDistributionProof;
use polymesh_dart::{curve_tree::*, *};

fn key_distribution_benchmark(c: &mut Criterion) {
    let mut rng = rand_chacha::ChaCha20Rng::from_seed([42; 32]);
    let nonce = b"key_distribution_benchmark";

    let params = get_account_curve_tree_parameters();

    let distributor = AccountKeys::rand(&mut rng).expect("Failed to generate distributor keys");
    let recipient = AccountKeys::rand(&mut rng).expect("Failed to generate recipient keys");

    // Benchmark: Generate KeyDistributionProof.
    c.bench_function("KeyDistributionProof generate", |b| {
        b.iter(|| {
            let _proof = KeyDistributionProof::<()>::new(
                &mut rng,
                black_box(&distributor.enc),
                vec![recipient.enc.public.clone()],
                nonce,
                params,
            )
            .expect("Failed to generate key distribution proof");
        })
    });

    // Generate a proof for verification/decryption benchmarks.
    let proof = KeyDistributionProof::<()>::new(
        &mut rng,
        &distributor.enc,
        vec![recipient.enc.public.clone()],
        nonce,
        params,
    )
    .expect("Failed to generate key distribution proof");

    // Benchmark: Verify KeyDistributionProof.
    c.bench_function("KeyDistributionProof verify", |b| {
        b.iter(|| {
            proof
                .verify(black_box(nonce), params, &mut rng)
                .expect("Failed to verify key distribution proof");
        })
    });

    // Benchmark: Decrypt the distributed secret key.
    c.bench_function("KeyDistributionProof decrypt", |b| {
        b.iter(|| {
            let _sk = proof
                .decrypt(black_box(0), &recipient.enc.secret)
                .expect("Failed to decrypt distributed key");
        })
    });
}

criterion_group!(key_distribution_benches, key_distribution_benchmark);
criterion_main!(key_distribution_benches);
