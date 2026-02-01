use ark_ec::CurveGroup;
use ark_pallas::Affine as PallasA;
use ark_serialize::CanonicalSerialize;
use ark_std::{UniformRand, format};
use blake2::Blake2b512;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use criterion::{Criterion, criterion_group, criterion_main};
use curve_tree_relations::curve_tree::CurveTree;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use polymesh_dart_bp::account::state::{AccountCommitmentKeyTrait, AccountState, NUM_GENERATORS};
use polymesh_dart_bp::account::{
    AccountStateTransitionProofBuilder, AccountStateTransitionProofVerifier,
};
use polymesh_dart_bp::account::state_transition_multi_new::MultiAssetStateTransitionProof;
use polymesh_dart_bp::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc, keygen_sig};
use polymesh_dart_bp::leg_new::{AssetCommitmentParams, AssetData, Leg, SettlementCreationProofNew};
use polymesh_dart_bp::poseidon_impls::poseidon_2::params::pallas::get_poseidon2_params_for_2_1_hashing;
use polymesh_dart_bp::util::{add_verification_tuples_batches_to_rmc, batch_verify_bp, verify_rmc};
use rand_core::CryptoRngCore;
use ark_ec_divisors::curves::{
    pallas::{PallasParams, Point as PallasPoint},
    vesta::{Point as VestaPoint, VestaParams},
};

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;
type PallasFr = ark_pallas::Fr;
type VestaFr = ark_vesta::Fr;

/// Setup commitment key
fn setup_comm_key(label: &[u8]) -> [PallasA; NUM_GENERATORS] {
    let account_comm_key: [PallasA; NUM_GENERATORS] = (0..NUM_GENERATORS)
        .map(|i| hash_to_pallas(label, format!("account-comm-{}", i).as_bytes()).into_affine())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    account_comm_key
}

/// Create new account
fn new_account<R: CryptoRngCore>(
    rng: &mut R,
    asset_id: u32,
    sk: SigKey<PallasA>,
    id: PallasFr,
) -> AccountState<PallasA> {
    let poseidon_config = get_poseidon2_params_for_2_1_hashing().unwrap();
    AccountState::new(rng, id, sk.0, asset_id, 0, poseidon_config).unwrap()
}

/// Create shared setup params
fn create_shared_setup<const NUM_GENS: usize>(
    label: &[u8],
) -> (
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    SelRerandProofParametersNew<VestaParameters, PallasParameters, VestaParams, PallasParams>,
    [PallasA; NUM_GENERATORS],
    PallasA,
    PallasA,
) {
    let account_tree_params =
        SelRerandProofParametersNew::<PallasParameters, VestaParameters, PallasParams, VestaParams>::new::<PallasPoint, VestaPoint>(
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    // Asset tree uses opposite curves
    let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, VestaParams, PallasParams>::new::<VestaPoint, PallasPoint>(
        NUM_GENS as u32,
        NUM_GENS as u32,
    )
    .unwrap();

    let account_comm_key = setup_comm_key(label);
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    (
        account_tree_params,
        asset_tree_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    )
}

/// Generate all keys needed for benchmarks
fn create_keys<R: CryptoRngCore>(
    rng: &mut R,
    account_comm_key: &[PallasA; NUM_GENERATORS],
    enc_key_gen: PallasA,
) -> (
    (SigKey<PallasA>, VerKey<PallasA>),
    (DecKey<PallasA>, EncKey<PallasA>),
    (SigKey<PallasA>, VerKey<PallasA>),
    (DecKey<PallasA>, EncKey<PallasA>),
    (DecKey<PallasA>, EncKey<PallasA>),
) {
    let (sk_s, pk_s) = keygen_sig(rng, account_comm_key.sk_gen());
    let (sk_s_e, pk_s_e) = keygen_enc(rng, enc_key_gen);

    let (sk_r, pk_r) = keygen_sig(rng, account_comm_key.sk_gen());
    let (sk_r_e, pk_r_e) = keygen_enc(rng, enc_key_gen);

    let (sk_a_e, pk_a_e) = keygen_enc(rng, enc_key_gen);

    (
        (sk_s, pk_s),
        (sk_s_e, pk_s_e),
        (sk_r, pk_r),
        (sk_r_e, pk_r_e),
        (sk_a_e, pk_a_e),
    )
}

/// Benchmark for large settlement
fn bench_settlement_multi_asset(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;
    const M: usize = 4;

    let height = 4;

    let label = b"bench";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, VestaParams, PallasParams>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        asset_tree_params.even_parameters.bp_gens(),
    );

    let asset_id = 1;

    // Setup keys for single sender/receiver pair
    let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

    // Auditor key
    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);

    let keys = vec![(true, pk_a_e.0)];

    // Create single asset data entry
    let asset_data = AssetData::new(
        asset_id,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.sl_params.delta,
    )
    .unwrap();

    let commitments = vec![asset_data.commitment];

    // Create the asset tree
    let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
        &commitments,
        &asset_tree_params,
        Some(height),
    );

    let root = asset_tree.root_node();
    let amount = 100;
    let nonce = b"large-settlement-bench";

    // Create legs with same asset, sender and receiver
    let num_legs: usize = 16;
    let mut legs = Vec::with_capacity(num_legs);
    let mut leg_encs = Vec::with_capacity(num_legs);
    let mut leg_enc_rands = Vec::with_capacity(num_legs);
    let mut asset_data_vec = Vec::with_capacity(num_legs);

    for _ in 0..num_legs {
        let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);
        asset_data_vec.push(asset_data.clone());
    }

    // All legs point to the same asset (index 0)
    let mut paths = Vec::new();
    for chunk in (0..num_legs).collect::<Vec<_>>().chunks(M) {
        let indices = vec![0; chunk.len()];
        let path = asset_tree.get_paths_to_leaves(&indices).unwrap();
        paths.push(path);
    }

    println!("L={L}, M={M}, asset tree height = {height} and {num_legs} legs");

    let proof = SettlementCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
        &mut rng,
        legs.clone(),
        leg_encs.clone(),
        leg_enc_rands.clone(),
        paths.clone(),
        asset_data_vec.clone(),
        &root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let proof_size = proof.compressed_size() + leg_encs.compressed_size();

    println!("Proof: {proof_size} bytes");

    // Benchmark proof generation
    c.bench_function("Large settlement proof generation", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let _ = SettlementCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
                &mut local_rng,
                legs.clone(),
                leg_encs.clone(),
                leg_enc_rands.clone(),
                paths.clone(),
                asset_data_vec.clone(),
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        });
    });

    // Benchmark proof verification
    c.bench_function("Large settlement proof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            proof
                .verify(
                    &mut local_rng,
                    leg_encs.clone(),
                    &root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        });
    });

    // Benchmark proof verification with RMC
    c.bench_function("Large settlement proof verification with RMC   ", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));

            proof
                .verify(
                    &mut local_rng,
                    leg_encs.clone(),
                    &root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    Some((&mut rmc_1, &mut rmc_0)),
                )
                .unwrap();
        });
    });
}

/// Benchmark for batch settlement verification
/// Creates multiple settlement proofs and verifies them in batch
fn bench_batch_settlement_verification(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 15;
    const L: usize = 64;
    const M: usize = 4;
    const BATCH_SIZE: usize = 20;

    let height = 4;

    let label = b"bench";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, VestaParams, PallasParams>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let mut all_asset_data = Vec::new();
    let mut commitments = Vec::new();

    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
    let keys = vec![(true, pk_a_e.0)];

    for i in 0..(M + 1) {
        let asset_id = (i + 1) as u32;
        let ad = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.sl_params.delta,
        )
        .unwrap();
        commitments.push(ad.commitment);
        all_asset_data.push(ad);
    }

    let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
        &commitments,
        &asset_tree_params,
        Some(height),
    );

    let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
    let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);
    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

    let root = asset_tree.root_node();
    let amount = 100;
    let nonces: Vec<Vec<u8>> = (0..BATCH_SIZE)
        .map(|i| format!("nonce_{}", i).into_bytes())
        .collect();

    // Create BATCH_SIZE settlements with varying number of legs (M-1, M, M+1)
    let mut proofs = Vec::with_capacity(BATCH_SIZE);
    let mut all_leg_encs = Vec::with_capacity(BATCH_SIZE);

    for i in 0..BATCH_SIZE {
        // Determine number of legs: M-1, M, or M+1 based on i % 3
        let num_legs = match i % 3 {
            0 => M - 1,
            1 => M,
            _ => M + 1,
        };

        let mut legs = Vec::new();
        let mut leg_encs = Vec::new();
        let mut leg_enc_rands = Vec::new();
        let mut leaf_paths = Vec::new();
        let mut asset_data = Vec::new();

        // Create legs for this settlement
        for j in 0..num_legs {
            let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, all_asset_data[j].id).unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
                .unwrap();

            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
            asset_data.push(all_asset_data[j].clone());
        }

        // Batch the indices into chunks of size M
        for chunk in (0..num_legs as u32)
            .into_iter()
            .collect::<Vec<_>>()
            .chunks(M)
        {
            let path = asset_tree.get_paths_to_leaves(chunk).unwrap();
            leaf_paths.push(path);
        }

        // Create the settlement proof
        let proof = SettlementCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
            &mut rng,
            legs,
            leg_encs.clone(),
            leg_enc_rands,
            leaf_paths,
            asset_data,
            &root,
            &nonces[i],
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        proofs.push(proof);
        all_leg_encs.push(leg_encs);
    }

    let total_legs: usize = all_leg_encs.iter().map(|e| e.len()).sum();
    println!(
        "L={L}, M={M}, height={height}, {BATCH_SIZE} settlement proofs with {total_legs} total legs",
    );

    // Benchmark batch verification with RMC
    c.bench_function("Batch settlement verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut even_tuples = Vec::with_capacity(BATCH_SIZE);
            let mut odd_tuples = Vec::with_capacity(BATCH_SIZE);
            let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));

            for i in 0..BATCH_SIZE {
                let (even, odd) = proofs[i]
                    .verify_and_return_tuples(
                        all_leg_encs[i].clone(),
                        &root,
                        &nonces[i],
                        &asset_tree_params,
                        &asset_comm_params,
                        enc_key_gen,
                        enc_gen,
                        &mut local_rng,
                        Some(&mut rmc_1),
                    )
                    .unwrap();
                even_tuples.push(even);
                odd_tuples.push(odd);
            }

            add_verification_tuples_batches_to_rmc(
                even_tuples,
                odd_tuples,
                asset_tree_params.even_parameters.pc_gens(),
                asset_tree_params.odd_parameters.pc_gens(),
                asset_tree_params.even_parameters.bp_gens(),
                asset_tree_params.odd_parameters.bp_gens(),
                &mut rmc_0,
                &mut rmc_1,
            )
            .unwrap();

            verify_rmc(&rmc_0, &rmc_1).unwrap();
        });
    });
}

/// Benchmark for large single-shot settlement
fn bench_single_shot_settlement_multi_asset(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 2;
    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;

    let (account_tree_params, asset_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        create_shared_setup::<NUM_GENS>(b"bench");

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        asset_tree_params.even_parameters.bp_gens(),
    );

    // Setup keys for Alice (sender), Bob (receiver), and auditor
    let (
        (sk_alice, pk_alice),
        (_sk_alice_e, pk_alice_e),
        (sk_bob, pk_bob),
        (_sk_bob_e, pk_bob_e),
        (_sk_auditor_e, pk_auditor_e),
    ) = create_keys(&mut rng, &account_comm_key, enc_key_gen);

    let num_legs = 16;
    let keys = vec![(true, pk_auditor_e.0)];
    let mut asset_data_vec = Vec::with_capacity(num_legs);
    let mut asset_commitments = Vec::with_capacity(num_legs);

    for asset_id in 1..=num_legs as u32 {
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.sl_params.delta,
        )
        .unwrap();
        asset_commitments.push(asset_data.commitment);
        asset_data_vec.push(asset_data);
    }

    let asset_tree_height = 3;
    let account_tree_height = 4;

    let asset_tree = CurveTree::<L, ASSET_TREE_M, VestaParameters, PallasParameters>::from_leaves(
        &asset_commitments,
        &asset_tree_params,
        Some(asset_tree_height),
    );
    let asset_tree_root = asset_tree.root_node();

    // Create legs, all with same sender (Alice) and receiver (Bob) but different assets
    let mut legs = Vec::with_capacity(num_legs);
    let mut leg_encs = Vec::with_capacity(num_legs);
    let mut leg_enc_rands = Vec::with_capacity(num_legs);
    let amount = 100;

    for asset_id in 1..=num_legs as u32 {
        let leg = Leg::new(pk_alice.0, pk_bob.0, keys.clone(), amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_bob_e.0, enc_key_gen, enc_gen)
            .unwrap();

        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);
    }

    // Get asset tree paths for all legs
    let mut asset_paths = Vec::new();
    for chunk in (0..num_legs).collect::<Vec<_>>().chunks(ASSET_TREE_M) {
        let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
        let path = asset_tree.get_paths_to_leaves(&indices).unwrap();
        asset_paths.push(path);
    }

    // Create Alice's accounts, one per asset
    let alice_id = PallasFr::rand(&mut rng);
    let mut alice_accounts = Vec::with_capacity(num_legs);
    let mut alice_account_comms = Vec::with_capacity(num_legs);

    for asset_id in 1..=num_legs as u32 {
        let mut account = new_account(&mut rng, asset_id, sk_alice.clone(), alice_id);
        account.balance = 500;
        let comm = account.commit(account_comm_key.clone()).unwrap();
        alice_account_comms.push(comm.0);
        alice_accounts.push(account);
    }

    // Create Bob's accounts, one per asset
    let bob_id = PallasFr::rand(&mut rng);
    let mut bob_accounts = Vec::with_capacity(num_legs);
    let mut bob_account_comms = Vec::with_capacity(num_legs);

    for asset_id in 1..=num_legs as u32 {
        let mut account = new_account(&mut rng, asset_id, sk_bob.clone(), bob_id);
        account.balance = 300;
        let comm = account.commit(account_comm_key.clone()).unwrap();
        bob_account_comms.push(comm.0);
        bob_accounts.push(account);
    }

    // Create account tree with all accounts
    let mut all_account_comms = Vec::with_capacity(2 * num_legs);
    all_account_comms.extend_from_slice(&alice_account_comms);
    all_account_comms.extend_from_slice(&bob_account_comms);

    let account_tree =
        CurveTree::<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>::from_leaves(
            &all_account_comms,
            &account_tree_params,
            Some(account_tree_height),
        );
    let account_tree_root = account_tree.root_node();

    let nonce = b"multi_asset_settlement_bench";

    println!(
        "L={L}, ASSET_TREE_M={ASSET_TREE_M}, ACCOUNT_TREE_M={ACCOUNT_TREE_M}, asset tree height = {asset_tree_height}, account tree height = {account_tree_height} and {num_legs} legs",
    );

    let settlement_proof = SettlementCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
        &mut rng,
        legs.clone(),
        leg_encs.clone(),
        leg_enc_rands.clone(),
        asset_paths.clone(),
        asset_data_vec.clone(),
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let settlement_proof_size = settlement_proof.compressed_size() + leg_encs.compressed_size();

    println!("Settlement proof: {settlement_proof_size} bytes");

    // Benchmark settlement proof generation
    c.bench_function("Multi-asset settlement proof generation", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let _ = SettlementCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
                &mut local_rng,
                legs.clone(),
                leg_encs.clone(),
                leg_enc_rands.clone(),
                asset_paths.clone(),
                asset_data_vec.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        });
    });

    // Benchmark settlement proof verification
    c.bench_function("Multi-asset settlement proof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            settlement_proof
                .verify(
                    &mut local_rng,
                    leg_encs.clone(),
                    &asset_tree_root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        });
    });

    // Benchmark settlement proof verification with RMC
    c.bench_function("Multi-asset settlement proof verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));

            settlement_proof
                .verify(
                    &mut local_rng,
                    leg_encs.clone(),
                    &asset_tree_root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    Some((&mut rmc_1, &mut rmc_0)),
                )
                .unwrap();
        });
    });

    // Create Alice's state transition proofs
    let mut alice_builders = Vec::with_capacity(num_legs);
    let mut alice_updated_comms = Vec::with_capacity(num_legs);

    for i in 0..num_legs {
        let updated_account = alice_accounts[i]
            .get_state_for_irreversible_send(amount)
            .unwrap();
        let updated_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        alice_updated_comms.push(updated_comm);

        let mut builder =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_accounts[i].clone(),
                updated_account,
                updated_comm,
                nonce,
            );
        builder.add_irreversible_send(amount, leg_encs[i].clone(), leg_enc_rands[i].clone());
        alice_builders.push(builder);
    }

    // Get paths for Alice's accounts
    let mut alice_paths = Vec::new();
    for chunk in (0..num_legs).collect::<Vec<_>>().chunks(ACCOUNT_TREE_M) {
        let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
        let path = account_tree.get_paths_to_leaves(&indices).unwrap();
        alice_paths.push(path);
    }

    // Measure Alice's (sender) proof generation
    let (alice_proof, alice_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
        &mut rng,
        alice_builders,
        alice_paths.clone(),
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let alice_proof_size = alice_proof.compressed_size();

    println!("Sender proof: {alice_proof_size} bytes");

    // Create Bob's state transition proofs
    let mut bob_builders = Vec::with_capacity(num_legs);
    let mut bob_updated_comms = Vec::with_capacity(num_legs);

    for i in 0..num_legs {
        let updated_account = bob_accounts[i]
            .get_state_for_irreversible_receive(amount)
            .unwrap();
        let updated_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        bob_updated_comms.push(updated_comm);

        let mut builder =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_accounts[i].clone(),
                updated_account,
                updated_comm,
                nonce,
            );
        builder.add_irreversible_receive(amount, leg_encs[i].clone(), leg_enc_rands[i].clone());
        bob_builders.push(builder);
    }

    // Get paths for Bob's accounts
    let mut bob_paths = Vec::new();
    for chunk in (num_legs..2 * num_legs)
        .collect::<Vec<_>>()
        .chunks(ACCOUNT_TREE_M)
    {
        let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
        let path = account_tree.get_paths_to_leaves(&indices).unwrap();
        bob_paths.push(path);
    }

    let (bob_proof, bob_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
        &mut rng,
        bob_builders,
        bob_paths.clone(),
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let bob_proof_size = bob_proof.compressed_size();

    println!("Receiver proof: {bob_proof_size} bytes");

    println!(
        "Total proof size: {} bytes\n",
        settlement_proof_size + alice_proof_size + bob_proof_size
    );

    // Benchmark full verification
    c.bench_function("Full verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();

            // Setup verifiers
            let mut alice_verifiers = Vec::new();
            for i in 0..num_legs {
                let mut verifier = AccountStateTransitionProofVerifier::<
                    L,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init(
                    alice_updated_comms[i], alice_nullifiers[i], nonce
                );
                verifier.add_irreversible_send(leg_encs[i].clone());
                alice_verifiers.push(verifier);
            }

            let mut bob_verifiers = Vec::new();
            for i in 0..num_legs {
                let mut verifier = AccountStateTransitionProofVerifier::<
                    L,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init(
                    bob_updated_comms[i], bob_nullifiers[i], nonce
                );
                verifier.add_irreversible_receive(leg_encs[i].clone());
                bob_verifiers.push(verifier);
            }

            let (settlement_even, settlement_odd) = settlement_proof
                .verify_and_return_tuples(
                    leg_encs.clone(),
                    &asset_tree_root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut local_rng,
                    None,
                )
                .unwrap();

            let (alice_even, alice_odd) = alice_proof
                .verify_and_return_tuples(
                    alice_verifiers,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut local_rng,
                    None,
                )
                .unwrap();

            let (bob_even, bob_odd) = bob_proof
                .verify_and_return_tuples(
                    bob_verifiers,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut local_rng,
                    None,
                )
                .unwrap();

            // Asset tree uses opposite curves than account tree
            let even_tuples = vec![settlement_odd, alice_even, bob_even];
            let odd_tuples = vec![settlement_even, alice_odd, bob_odd];

            batch_verify_bp(even_tuples, odd_tuples, account_tree_params.even_parameters.pc_gens(), account_tree_params.odd_parameters.pc_gens(), account_tree_params.even_parameters.bp_gens(), account_tree_params.odd_parameters.bp_gens()).unwrap();
        });
    });

    // Benchmark full verification with RMC
    c.bench_function("Full verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));

            // Setup verifiers
            let mut alice_verifiers = Vec::new();
            for i in 0..num_legs {
                let mut verifier = AccountStateTransitionProofVerifier::<
                    L,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init(
                    alice_updated_comms[i], alice_nullifiers[i], nonce
                );
                verifier.add_irreversible_send(leg_encs[i].clone());
                alice_verifiers.push(verifier);
            }

            let mut bob_verifiers = Vec::new();
            for i in 0..num_legs {
                let mut verifier = AccountStateTransitionProofVerifier::<
                    L,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init(
                    bob_updated_comms[i], bob_nullifiers[i], nonce
                );
                verifier.add_irreversible_receive(leg_encs[i].clone());
                bob_verifiers.push(verifier);
            }

            let (settlement_even, settlement_odd) = settlement_proof
                .verify_and_return_tuples(
                    leg_encs.clone(),
                    &asset_tree_root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut local_rng,
                    Some(&mut rmc_0),
                )
                .unwrap();

            let (alice_even, alice_odd) = alice_proof
                .verify_and_return_tuples(
                    alice_verifiers,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut local_rng,
                    Some(&mut rmc_0),
                )
                .unwrap();

            let (bob_even, bob_odd) = bob_proof
                .verify_and_return_tuples(
                    bob_verifiers,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut local_rng,
                    Some(&mut rmc_0),
                )
                .unwrap();

            // Asset tree uses opposite curves than account tree
            let even_tuples = vec![settlement_odd, alice_even, bob_even];
            let odd_tuples = vec![settlement_even, alice_odd, bob_odd];

            add_verification_tuples_batches_to_rmc(
                even_tuples,
                odd_tuples,
                account_tree_params.even_parameters.pc_gens(),
                account_tree_params.odd_parameters.pc_gens(),
                account_tree_params.even_parameters.bp_gens(),
                account_tree_params.odd_parameters.bp_gens(),
                &mut rmc_0,
                &mut rmc_1,
            )
            .unwrap();

            verify_rmc(&rmc_0, &rmc_1).unwrap();
        });
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(10);
    targets = bench_settlement_multi_asset,
        bench_batch_settlement_verification,
        bench_single_shot_settlement_multi_asset
}
criterion_main!(benches);
