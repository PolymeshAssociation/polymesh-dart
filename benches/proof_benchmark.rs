use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use polymesh_dart::{curve_tree::*, *};

fn proof_benchmark(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let mut asset_tree = AssetCurveTree::new().expect("Failed to create asset tree");
    let mut asset_roots =
        RootHistory::<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>::new(10, asset_tree.params());

    // The account curve tree.
    let mut account_tree =
        ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
            ACCOUNT_TREE_HEIGHT,
            ACCOUNT_TREE_GENS,
        )
        .expect("Failed to create account tree");
    let account_params = account_tree.params().clone();
    let mut account_roots =
        RootHistory::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(10, &account_params);

    let issuer_keys = AccountKeys::rand(&mut rng).expect("Failed to generate issuer keys");
    let issuer_acct = issuer_keys.public_keys();
    let investor_keys = AccountKeys::rand(&mut rng).expect("Failed to generate investor keys");
    let investor1_acct = investor_keys.public_keys();
    let mediator_keys = AccountKeys::rand(&mut rng).expect("Failed to generate mediator keys");
    let mediator_acct = mediator_keys.public_keys();
    let ctx = b"benchmark";

    let asset_id = 0 as _;
    let asset_state = AssetState::new(asset_id, &[], &[mediator_acct.enc]);

    // Create the asset.
    asset_tree
        .set_asset_state(asset_state.clone())
        .expect("Failed to insert asset state into asset tree");
    asset_roots.add_root(
        (&asset_tree)
            .root_node()
            .expect("Failed to get asset tree root"),
    );

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
    let leaf = account_state
        .current_state_commitment
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
    let leaf = investor_account_state
        .current_state_commitment
        .as_leaf_value()
        .expect("Failed to get leaf value from asset state commitment");
    account_tree
        .insert(leaf)
        .expect("Failed to insert asset state commitment into account tree");

    // Update account tree roots.
    account_roots.add_root(
        (&account_tree)
            .root_node()
            .expect("Failed to get account tree root"),
    );

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
                .verify(black_box(&account_roots), &mut rng)
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
    account_roots.add_root(
        (&account_tree)
            .root_node()
            .expect("Failed to get account tree root"),
    );

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
                .verify(black_box(&asset_roots), &mut rng)
                .expect("Failed to verify settlement proof");
        })
    });

    let leg_enc = settlement.legs[0]
        .leg_enc()
        .expect("Failed to get leg encoding from settlement proof");
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
                .verify(&leg_enc, black_box(&account_roots), &mut rng)
                .expect("Failed to verify sender affirmation proof");
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
                .verify(&leg_enc, black_box(&account_roots), &mut rng)
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
    account_roots.add_root(
        (&account_tree)
            .root_node()
            .expect("Failed to get account tree root"),
    );

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
                .verify(&leg_enc, black_box(&account_roots), &mut rng)
                .expect("Failed to verify receiver claim assets proof");
        })
    });
}

criterion_group!(proof_benches, proof_benchmark);
criterion_main!(proof_benches);
