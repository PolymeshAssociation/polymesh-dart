use criterion::{Criterion, criterion_group, criterion_main};
use rand::SeedableRng;
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use std::hint::black_box;

use polymesh_dart::{curve_tree::*, *};

fn proof_benchmark(c: &mut Criterion) {
    let mut rng = rand_chacha::ChaCha20Rng::from_seed([42; 32]);
    let mut asset_tree = AssetCurveTree::new().expect("Failed to create asset tree");

    // The account curve tree.
    let mut account_tree =
        ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
            ACCOUNT_TREE_HEIGHT,
            ACCOUNT_TREE_GENS,
        )
        .expect("Failed to create account tree");
    let account_params = account_tree.params().clone();

    let issuer_keys = AccountKeys::rand(&mut rng).expect("Failed to generate issuer keys");
    let issuer_acct = issuer_keys.public_keys();
    let investor_keys = AccountKeys::rand(&mut rng).expect("Failed to generate investor keys");
    let investor1_acct = investor_keys.public_keys();
    let mediator_keys = AccountKeys::rand(&mut rng).expect("Failed to generate mediator keys");
    let mediator_acct = mediator_keys.public_keys();
    let ctx = b"benchmark";

    let asset_id = 0 as _;
    let asset_state = AssetState::new(asset_id, &[mediator_acct.enc], &[]);

    // Create the asset.
    asset_tree
        .set_asset_state(asset_state.clone())
        .expect("Failed to insert asset state into asset tree");
    let asset_root = asset_tree.root().expect("Failed to get asset tree root");

    // Benchmark: Generate account asset registration proof.
    c.bench_function("AccountAssetRegistrationProof generate", |b| {
        b.iter(|| {
            let (_proof, mut _account_state) = AccountAssetRegistrationProof::new(
                &mut rng,
                black_box(&issuer_keys.acct),
                asset_id,
                0,
                ctx,
                &account_params,
            )
            .expect("Failed to generate proof");
        })
    });

    // Generate a proof to benchmark verification.
    let (proof, mut account_state) = AccountAssetRegistrationProof::new(
        &mut rng,
        black_box(&issuer_keys.acct),
        asset_id,
        0,
        ctx,
        &account_params,
    )
    .expect("Failed to generate proof");
    account_state
        .commit_pending_state()
        .expect("Failed to commit pending state");
    let current_commitment = account_state
        .current_commitment(&issuer_keys.acct)
        .expect("Failed to get current commitment");
    let leaf = current_commitment
        .as_leaf_value()
        .expect("Failed to get leaf value from asset state commitment");
    account_tree
        .insert(leaf)
        .expect("Failed to insert asset state commitment into account tree");

    // Benchmark: Verify account asset registration proof.
    c.bench_function("AccountAssetRegistrationProof verify", |b| {
        b.iter(|| {
            proof
                .verify(black_box(ctx), &account_params, &mut rng)
                .expect("Failed to verify proof");
        })
    });

    // Generate a batch of account asset registration proofs to benchmark batched verification.
    for num_proofs in [1u32, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 100] {
        let mut account_assets = Vec::with_capacity(NUM_PROOFS);
        for idx in 0..num_proofs {
            account_assets.push((issuer_keys.acct.clone(), idx as AssetId, 0));
        }
        let (proof, _) = BatchedAccountAssetRegistrationProof::<()>::new(
            &mut rng,
            &account_assets,
            ctx,
            &account_params,
        )
        .expect("Failed to generate batched proof");

        // Benchmark: Verify batched account asset registration proof.
        let name = format!("BatchedAccountAssetRegistrationProof verify {num_proofs}");
        c.bench_function(&name, |b| {
            b.iter(|| {
                proof
                    .verify(black_box(ctx), &account_params, &mut rng)
                    .expect("Failed to verify proof");
            })
        });

        // Benchmark: Batched_verify batched account asset registration proof.
        let name = format!("BatchedAccountAssetRegistrationProof batched_verify {num_proofs}");
        c.bench_function(&name, |b| {
            b.iter(|| {
                proof
                    .batched_verify(black_box(ctx), &account_params, &mut rng)
                    .expect("Failed to verify proof");
            })
        });
    }

    // Register the investor's account state.
    let (_proof, mut investor_account_state) = AccountAssetRegistrationProof::new(
        &mut rng,
        &investor_keys.acct,
        asset_id,
        0,
        ctx,
        &account_params,
    )
    .expect("Failed to generate proof");
    investor_account_state
        .commit_pending_state()
        .expect("Failed to commit pending state");
    let current_commitment = investor_account_state
        .current_commitment(&investor_keys.acct)
        .expect("Failed to get current commitment");
    let leaf = current_commitment
        .as_leaf_value()
        .expect("Failed to get leaf value from asset state commitment");
    account_tree
        .insert(leaf)
        .expect("Failed to insert asset state commitment into account tree");

    // Update account tree roots.
    let account_root = (&account_tree)
        .root()
        .expect("Failed to get account tree root");

    // Benchmark: Generate asset minting proof.
    let mint_amount = 1000u64;
    let leg_amount = 500u64;
    c.bench_function("AssetMintingProof generate", |b| {
        b.iter(|| {
            let _proof = AssetMintingProof::new(
                &mut rng,
                &issuer_keys.acct,
                &mut account_state,
                &account_tree,
                mint_amount,
            )
            .expect("Failed to generate asset minting proof");
        })
    });

    // Generate a proof to benchmark verification.
    let proof = AssetMintingProof::new(
        &mut rng,
        &issuer_keys.acct,
        &mut account_state,
        &account_tree,
        mint_amount,
    )
    .expect("Failed to generate asset minting proof");

    // Benchmark: Verify asset minting proof.
    c.bench_function("AssetMintingProof verify", |b| {
        b.iter(|| {
            proof
                .verify(ctx, black_box(&account_root), &mut rng)
                .expect("Failed to verify proof");
        })
    });

    // Add the asset minting to the account state.
    account_state
        .commit_pending_state()
        .expect("Failed to commit pending state");
    account_tree
        .insert(
            proof
                .updated_account_state_commitment
                .as_leaf_value()
                .expect("Failed to get leaf value from asset state commitment"),
        )
        .expect("Failed to insert updated account state commitment into account tree");
    let account_root = (&account_tree)
        .root()
        .expect("Failed to get account tree root");

    // Benchmark: Generate settlement creation proof.
    c.bench_function("SettlementProof generate", |b| {
        b.iter(|| {
            let _settlement: SettlementProof<(), AssetTreeConfig> = SettlementBuilder::new(b"Test")
                .leg(black_box(LegBuilder {
                    sender: issuer_acct,
                    receiver: investor1_acct,
                    asset: asset_state.clone(),
                    amount: leg_amount,
                }))
                .encrypt_and_prove(&mut rng, &asset_tree.tree)
                .expect("Failed to create settlement");
        })
    });

    // Generate a proof to benchmark verification.
    let settlement: SettlementProof = SettlementBuilder::new(b"Test")
        .leg(LegBuilder {
            sender: issuer_acct,
            receiver: investor1_acct,
            asset: asset_state.clone(),
            amount: leg_amount,
        })
        .encrypt_and_prove(&mut rng, &asset_tree.tree)
        .expect("Failed to create settlement");

    // Benchmark: Verify settlement proof.
    c.bench_function("SettlementProof verify", |b| {
        b.iter(|| {
            settlement
                .verify(black_box(&asset_root), &mut rng)
                .expect("Failed to verify settlement proof");
        })
    });

    let leg_enc = settlement.legs[0].leg_enc.clone();
    let leg_enc_rand = leg_enc
        .get_encryption_randomness(LegRole::Sender, &issuer_keys.enc)
        .expect("Failed to decrypt sender's secret key");
    let leg_ref = LegRef::new(0.into(), 0 as _);

    // Benchmark: Generate of sender affirmation proof.
    c.bench_function("SenderAffirmationProof generate", |b| {
        b.iter(|| {
            let _proof: SenderAffirmationProof = SenderAffirmationProof::new(
                &mut rng,
                &issuer_keys.acct,
                &leg_ref,
                leg_amount,
                &leg_enc,
                &leg_enc_rand,
                &mut account_state,
                &account_tree,
            )
            .expect("Failed to generate sender affirmation proof");
        })
    });

    // Generate a proof to benchmark verification.
    let proof: SenderAffirmationProof = SenderAffirmationProof::new(
        &mut rng,
        &issuer_keys.acct,
        &leg_ref,
        leg_amount,
        &leg_enc,
        &leg_enc_rand,
        &mut account_state,
        &account_tree,
    )
    .expect("Failed to generate sender affirmation proof");

    // Benchmark: Verify sender affirmation proof.
    c.bench_function("SenderAffirmationProof verify", |b| {
        b.iter(|| {
            proof
                .verify(&leg_enc, black_box(&account_root), &mut rng)
                .expect("Failed to verify sender affirmation proof");
        })
    });

    // Generate multiple sender affirmation proofs to benchmark parallel verification.
    const NUM_PROOFS: usize = 100;
    #[cfg(feature = "parallel")]
    let proofs = (0..NUM_PROOFS)
        .into_par_iter()
        .map(|_| {
            let mut rng = rand::thread_rng();
            let mut account_state = account_state.clone();
            SenderAffirmationProof::new(
                &mut rng,
                &issuer_keys.acct,
                &leg_ref,
                leg_amount,
                &leg_enc,
                &leg_enc_rand,
                &mut account_state,
                &account_tree,
            )
            .expect("Failed to generate sender affirmation proof")
        })
        .collect::<Vec<_>>();

    #[cfg(not(feature = "parallel"))]
    {
        let mut proofs = Vec::new();
        for _ in 0..NUM_PROOFS {
            proofs.push(
                SenderAffirmationProof::new(
                    &mut rng,
                    &issuer_keys.acct,
                    &leg_ref,
                    leg_amount,
                    &leg_enc,
                    &leg_enc_rand,
                    &mut account_state,
                    &account_tree,
                )
                .expect("Failed to generate sender affirmation proof"),
            );
        }
        proofs
    }

    // Benchmark: Parallel verification of sender affirmation proofs.
    c.bench_function("Parallel SenderAffirmationProof verify 10", |b| {
        b.iter(|| {
            #[cfg(feature = "parallel")]
            {
                proofs[0..10].par_iter().for_each(|proof| {
                    let mut rng = rand::thread_rng();
                    proof
                        .verify(&leg_enc, black_box(&account_root), &mut rng)
                        .expect("Failed to verify sender affirmation proof");
                });
            }
            #[cfg(not(feature = "parallel"))]
            {
                proofs[0..10].iter().for_each(|proof| {
                    proof
                        .verify(&leg_enc, black_box(&account_root), &mut rng)
                        .expect("Failed to verify sender affirmation proof");
                });
            }
        })
    });

    // Benchmark: Parallel verification of sender affirmation proofs.
    c.bench_function("Parallel SenderAffirmationProof verify 100", |b| {
        b.iter(|| {
            #[cfg(feature = "parallel")]
            {
                proofs.par_iter().for_each(|proof| {
                    let mut rng = rand::thread_rng();
                    proof
                        .verify(&leg_enc, black_box(&account_root), &mut rng)
                        .expect("Failed to verify sender affirmation proof");
                });
            }
            #[cfg(not(feature = "parallel"))]
            {
                proofs.iter().for_each(|proof| {
                    proof
                        .verify(&leg_enc, black_box(&account_root), &mut rng)
                        .expect("Failed to verify sender affirmation proof");
                });
            }
        })
    });

    // Benchmark: Generate of receiver affirmation proof.
    c.bench_function("ReceiverAffirmationProof generate", |b| {
        b.iter(|| {
            let _proof: ReceiverAffirmationProof = ReceiverAffirmationProof::new(
                &mut rng,
                &investor_keys.acct,
                &leg_ref,
                &leg_enc,
                &leg_enc_rand,
                &mut investor_account_state,
                &account_tree,
            )
            .expect("Failed to generate receiver affirmation proof");
        })
    });

    // Generate a proof to benchmark verification.
    let proof: ReceiverAffirmationProof = ReceiverAffirmationProof::new(
        &mut rng,
        &investor_keys.acct,
        &leg_ref,
        &leg_enc,
        &leg_enc_rand,
        &mut investor_account_state,
        &account_tree,
    )
    .expect("Failed to generate receiver affirmation proof");

    // Benchmark: Verify receiver affirmation proof.
    c.bench_function("ReceiverAffirmationProof verify", |b| {
        b.iter(|| {
            proof
                .verify(&leg_enc, black_box(&account_root), &mut rng)
                .expect("Failed to verify receiver affirmation proof");
        })
    });

    // Update the receiver's account state.
    investor_account_state
        .commit_pending_state()
        .expect("Failed to commit pending state");
    account_tree
        .insert(
            proof
                .updated_account_state_commitment
                .as_leaf_value()
                .expect("Failed to get leaf value from asset state commitment"),
        )
        .expect("Failed to insert updated account state commitment into account tree");
    let account_root = (&account_tree)
        .root()
        .expect("Failed to get account tree root");

    // Benchmark: Generate mediator affirmation proof.
    c.bench_function("MediatorAffirmationProof generate", |b| {
        b.iter(|| {
            let _proof = MediatorAffirmationProof::new(
                &mut rng,
                &leg_ref,
                asset_id,
                &leg_enc,
                &mediator_keys.enc,
                0,
                true,
            )
            .expect("Failed to generate mediator affirmation proof");
        })
    });

    // Generate a proof to benchmark verification.
    let proof = MediatorAffirmationProof::new(
        &mut rng,
        &leg_ref,
        asset_id,
        &leg_enc,
        &mediator_keys.enc,
        0,
        true,
    )
    .expect("Failed to generate mediator affirmation proof");

    // Benchmark: Verify mediator affirmation proof.
    c.bench_function("MediatorAffirmationProof verify", |b| {
        b.iter(|| {
            proof
                .verify(&leg_enc)
                .expect("Failed to verify mediator affirmation proof");
        })
    });

    // Benchmark: Generate receiver claim assets proof.
    c.bench_function("ReceiverClaimProof generate", |b| {
        b.iter(|| {
            let _proof: ReceiverClaimProof = ReceiverClaimProof::new(
                &mut rng,
                &investor_keys.acct,
                &leg_ref,
                leg_amount,
                &leg_enc,
                &leg_enc_rand,
                &mut investor_account_state,
                &account_tree,
            )
            .expect("Failed to generate receiver claim assets proof");
        })
    });

    // Generate a proof to benchmark verification.
    let proof: ReceiverClaimProof = ReceiverClaimProof::new(
        &mut rng,
        &investor_keys.acct,
        &leg_ref,
        leg_amount,
        &leg_enc,
        &leg_enc_rand,
        &mut investor_account_state,
        &account_tree,
    )
    .expect("Failed to generate receiver claim assets proof");

    // Benchmark: Verify receiver claim assets proof.
    c.bench_function("ReceiverClaimProof verify", |b| {
        b.iter(|| {
            proof
                .verify(&leg_enc, black_box(&account_root), &mut rng)
                .expect("Failed to verify receiver claim assets proof");
        })
    });
}

criterion_group!(proof_benches, proof_benchmark);
criterion_main!(proof_benches);
