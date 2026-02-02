use crate::account::*;
use crate::account_registration::tests::{new_account, setup_comm_key};
use crate::leg_old::tests::setup_keys;
use crate::leg_old::{
    AssetCommitmentParams, AssetData, Leg,
    LegEncryption, LegEncryptionRandomness, MediatorTxnProof, MEDIATOR_TXN_LABEL
    ,
};
use ark_ec::CurveGroup;
use ark_std::UniformRand;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::curve_tree::CurveTree;
use curve_tree_relations::parameters::SelRerandProofParameters;
use crate::account::tests_new_ct;

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;
type PallasA = ark_pallas::Affine;
type PallasFr = ark_pallas::Fr;
type VestaFr = ark_vesta::Fr;

/// Setup parameters for old proof protocol
pub fn setup_gens<const NUM_GENS: usize>(
    label: &[u8],
) -> (
    SelRerandProofParameters<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
    PallasA,
) {
    // Create public params with lookup tables for old proof protocol
    let account_tree_params = SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
        NUM_GENS as u32,
        NUM_GENS as u32,
    )
    .unwrap();
    let account_comm_key = setup_comm_key(label);
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();
    (account_tree_params, account_comm_key, enc_key_gen, enc_gen)
}

/// Setup asset and account params for old proof protocol
pub fn setup_asset_and_account_params<const NUM_GENS: usize>() -> (
    SelRerandProofParameters<PallasParameters, VestaParameters>,
    SelRerandProofParameters<VestaParameters, PallasParameters>,
    AssetCommitmentParams<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
    PallasA,
) {
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_tree_params = SelRerandProofParameters::<VestaParameters, PallasParameters>::new(
        NUM_GENS as u32,
        NUM_GENS as u32,
    )
    .unwrap();

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        account_tree_params.odd_parameters.bp_gens(),
    );

    (
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    )
}

pub fn setup_single_leg_settlement<const NUM_GENS: usize, const L: usize>(
    asset_tree_height: u64,
    account_tree_height: u64,
) -> (
    AssetData<PallasFr, VestaFr, PallasParameters, VestaParameters>,
    CurveTreeWitnessPath<L, VestaParameters, PallasParameters>,
    Root<L, 1, VestaParameters, PallasParameters>,
    Leg<PallasA>,
    LegEncryption<PallasA>,
    LegEncryptionRandomness<PallasFr>,
    AccountState<PallasA>,
    AccountState<PallasA>,
    AccountState<PallasA>,
    AccountState<PallasA>,
    AccountStateCommitment<PallasA>,
    AccountStateCommitment<PallasA>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
    SelRerandProofParameters<PallasParameters, VestaParameters>,
    SelRerandProofParameters<VestaParameters, PallasParameters>,
    AssetCommitmentParams<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
    PallasA,
) {
    let (
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_asset_and_account_params::<NUM_GENS>();

    let asset_tree_delta = asset_tree_params.odd_parameters.sl_params.delta;

    tests_new_ct::setup_single_leg_settlement_common(
        asset_tree_height,
        account_tree_height,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
        asset_tree_delta,
    )
}

/// Helper function to setup multi-asset settlement scenario with multiple legs.
fn setup_multi_asset_settlement<
    const NUM_GENS: usize,
    const L: usize,
    const ASSET_TREE_M: usize,
    const ACCOUNT_TREE_M: usize,
>(
    num_legs: usize,
    asset_tree_height: usize,
    account_tree_height: usize,
) -> (
    Vec<AssetData<PallasFr, VestaFr, PallasParameters, VestaParameters>>,
    Vec<CurveTreeWitnessMultiPath<L, ASSET_TREE_M, VestaParameters, PallasParameters>>,
    Root<L, ASSET_TREE_M, VestaParameters, PallasParameters>,
    Vec<Leg<PallasA>>,
    Vec<LegEncryption<PallasA>>,
    Vec<LegEncryptionRandomness<PallasFr>>,
    Vec<AccountState<PallasA>>,
    Vec<AccountState<PallasA>>,
    Vec<CurveTreeWitnessMultiPath<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>>,
    Vec<CurveTreeWitnessMultiPath<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>>,
    Root<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>,
    SelRerandProofParameters<PallasParameters, VestaParameters>,
    SelRerandProofParameters<VestaParameters, PallasParameters>,
    AssetCommitmentParams<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
    PallasA,
) {
    let mut rng = rand::thread_rng();

    let (
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_asset_and_account_params::<NUM_GENS>();

    let (
        ((sk_alice, pk_alice), (_, pk_alice_e)),
        ((sk_bob, pk_bob), (_, pk_bob_e)),
        (_, (_, pk_auditor_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

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

    let asset_tree = CurveTree::<L, ASSET_TREE_M, VestaParameters, PallasParameters>::from_leaves(
        &asset_commitments,
        &asset_tree_params,
        Some(asset_tree_height),
    );
    let asset_tree_root = asset_tree.root_node();

    let mut legs = Vec::with_capacity(num_legs);
    let mut leg_encs = Vec::with_capacity(num_legs);
    let mut leg_enc_rands = Vec::with_capacity(num_legs);
    let amount = 100;

    for asset_id in 1..=num_legs as u32 {
        let (leg, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            amount,
            asset_id,
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);
    }

    let mut asset_paths = Vec::new();
    for chunk in (0..num_legs).collect::<Vec<_>>().chunks(ASSET_TREE_M) {
        let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
        let path = asset_tree.get_paths_to_leaves(&indices).unwrap();
        asset_paths.push(path);
    }

    let alice_id = PallasFr::rand(&mut rng);
    let mut alice_accounts = Vec::with_capacity(num_legs);
    let mut alice_account_comms = Vec::with_capacity(num_legs);

    for asset_id in 1..=num_legs as u32 {
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_alice.clone(), alice_id);
        account.balance = 500;
        let comm = account.commit(account_comm_key.clone()).unwrap();
        alice_account_comms.push(comm.0);
        alice_accounts.push(account);
    }

    let bob_id = PallasFr::rand(&mut rng);
    let mut bob_accounts = Vec::with_capacity(num_legs);
    let mut bob_account_comms = Vec::with_capacity(num_legs);

    for asset_id in 1..=num_legs as u32 {
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_bob.clone(), bob_id);
        account.balance = 300;
        let comm = account.commit(account_comm_key.clone()).unwrap();
        bob_account_comms.push(comm.0);
        bob_accounts.push(account);
    }

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

    // Get paths for Alice's accounts in batches
    let mut alice_paths = Vec::new();
    for chunk in (0..num_legs).collect::<Vec<_>>().chunks(ACCOUNT_TREE_M) {
        let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
        let path = account_tree.get_paths_to_leaves(&indices).unwrap();
        alice_paths.push(path);
    }

    // Get paths for Bob's accounts in batches
    let mut bob_paths = Vec::new();
    for chunk in (0..num_legs).collect::<Vec<_>>().chunks(ACCOUNT_TREE_M) {
        let indices: Vec<_> = chunk.iter().map(|&i| (num_legs + i) as u32).collect();
        let path = account_tree.get_paths_to_leaves(&indices).unwrap();
        bob_paths.push(path);
    }

    (
        asset_data_vec,
        asset_paths,
        asset_tree_root,
        legs,
        leg_encs,
        leg_enc_rands,
        alice_accounts,
        bob_accounts,
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    )
}

#[cfg(NEVER)]
fn send_txn() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (((sk_s, pk_s), (_, pk_s_e)), ((_, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Sender account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
    // Assume that account had some balance. Either got it as the issuer or from another transfer
    account.balance = 200;

    let account_tree = tests_new_ct::get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        4,
    )
    .unwrap();

    // Setup ends. Sender and verifier interaction begins below

    let nonce = b"test-nonce";

    let clock = Instant::now();

    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsSenderTxnProof::new(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let prover_time = clock.elapsed();

    let clock = Instant::now();

    proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    proof
        .verify(
            &mut rng,
            leg_enc,
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_0, &mut rmc_1)),
        )
        .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verifier_time_rmc = clock.elapsed();

    println!("L={L}, height={}", account_tree.height());
    println!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[cfg(NEVER)]
fn receive_txn() {
    let mut rng = rand::thread_rng();

    // Setup beings

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (((_, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Receiver account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
    // Assume that account had some balance. Either got it as the issuer or from another transfer
    account.balance = 200;
    let account_tree = tests_new_ct::get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        4,
    )
    .unwrap();

    // Setup ends. Receiver and verifier interaction begins below

    let nonce = b"test-nonce";

    let clock = Instant::now();

    let updated_account = account.get_state_for_receive();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsReceiverTxnProof::new(
        &mut rng,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let prover_time = clock.elapsed();

    let clock = Instant::now();

    proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    proof
        .verify(
            &mut rng,
            leg_enc,
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_0, &mut rmc_1)),
        )
        .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verifier_time_rmc = clock.elapsed();

    println!("L={L}, height={}", account_tree.height());
    println!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[cfg(NEVER)]
fn claim_received_funds() {
    // This is what report calls txn_cu (counter update) done by receiver
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (
        ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
        ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
        ((_, _), (_, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Receiver account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
    // Assume that account had some balance and it had sent the receive transaction to increase its counter
    account.balance = 200;
    account.counter += 1;

    let account_tree = tests_new_ct::get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        4,
    )
    .unwrap();

    let nonce = b"test-nonce";

    let clock = Instant::now();

    let updated_account = account.get_state_for_claiming_received(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let root = account_tree.root_node();

    let (proof, nullifier) = ClaimReceivedTxnProof::new(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let prover_time = clock.elapsed();

    let clock = Instant::now();

    proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    proof
        .verify(
            &mut rng,
            leg_enc,
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_0, &mut rmc_1)),
        )
        .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verifier_time_rmc = clock.elapsed();

    log::info!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[cfg(NEVER)]
fn counter_update_txn_by_sender() {
    // This is similar to receive txn as only account's counter is decreased, balance remains same.

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (
        ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
        ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
        ((_, _), (_, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Sender account with non-zero counter
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
    account.balance = 50;
    account.counter = 1;

    let account_tree = tests_new_ct::get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        4,
    )
    .unwrap();

    let nonce = b"test-nonce";

    let clock = Instant::now();

    let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let root = account_tree.root_node();

    let (proof, nullifier) = SenderCounterUpdateTxnProof::new(
        &mut rng,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let prover_time = clock.elapsed();

    let clock = Instant::now();

    proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    proof
        .verify(
            &mut rng,
            leg_enc,
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_0, &mut rmc_1)),
        )
        .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verifier_time_rmc = clock.elapsed();

    log::info!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[cfg(NEVER)]
fn reverse_send_txn() {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (
        ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
        ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
        ((_, _), (_, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Sender account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
    // Assume that account had some balance and it had sent the send transaction to increase its counter
    account.balance = 200;
    account.counter += 1;

    let account_tree = tests_new_ct::get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        4,
    )
    .unwrap();

    let nonce = b"test-nonce";

    let clock = Instant::now();

    let updated_account = account.get_state_for_reversing_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let root = account_tree.root_node();

    let (proof, nullifier) = SenderReverseTxnProof::new(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let prover_time = clock.elapsed();

    let clock = Instant::now();

    proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    proof
        .verify(
            &mut rng,
            leg_enc,
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_0, &mut rmc_1)),
        )
        .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verifier_time_rmc = clock.elapsed();

    log::info!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[cfg(NEVER)]
fn reverse_receive_txn() {
    // This is similar to receive txn as only account's counter is decreased, balance remains same.

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (((_, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_leg, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Receiver account with non-zero counter
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
    account.balance = 50;
    account.counter = 1;

    let account_tree = tests_new_ct::get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        4,
    )
    .unwrap();

    let nonce = b"test-nonce";

    let clock = Instant::now();

    let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let root = account_tree.root_node();

    let (proof, nullifier) = ReceiverCounterUpdateTxnProof::new(
        &mut rng,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let prover_time = clock.elapsed();

    let clock = Instant::now();

    proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    proof
        .verify(
            &mut rng,
            leg_enc,
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_0, &mut rmc_1)),
        )
        .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verifier_time_rmc = clock.elapsed();

    log::info!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[cfg(NEVER)]
fn batch_send_txn_proofs() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 10;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);
    let mut leg_enc_rands = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let ((sk_s, pk_s), (_, pk_s_e)) = &all_keys[i].0;
        let ((_, pk_r), (_, pk_r_e)) = &all_keys[i].1;
        let ((_, _), (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);

        // Create sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s.clone(), id);
        account.balance = 200; // Ensure sufficient balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(3),
    );

    for i in 0..batch_size {
        let updated_account = accounts[i].get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

        updated_accounts.push(updated_account);
        updated_account_comms.push(updated_account_comm);
        paths.push(path);
    }

    let root = account_tree.root_node();

    let nonces: Vec<Vec<u8>> = (0..batch_size)
        .map(|i| format!("batch_send_nonce_{}", i).into_bytes())
        .collect();

    let mut proofs = Vec::with_capacity(batch_size);
    let mut nullifiers = Vec::with_capacity(batch_size);

    for i in 0..batch_size {
        let (proof, nullifier) = AffirmAsSenderTxnProof::new(
            &mut rng,
            amount,
            leg_encs[i].clone(),
            leg_enc_rands[i].clone(),
            &accounts[i],
            &updated_accounts[i],
            updated_account_comms[i],
            paths[i].clone(),
            &root,
            &nonces[i],
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        proofs.push(proof);
        nullifiers.push(nullifier);
    }

    let clock = Instant::now();

    for i in 0..batch_size {
        proofs[i]
            .verify(
                &mut rng,
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
    }

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut even_tuples = Vec::with_capacity(batch_size);
    let mut odd_tuples = Vec::with_capacity(batch_size);

    // These can also be done in parallel
    for i in 0..batch_size {
        let (even, odd) = proofs[i]
            .verify_and_return_tuples(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();
        even_tuples.push(even);
        odd_tuples.push(odd);
    }

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let batch_verifier_time = clock.elapsed();

    println!(
        "For {batch_size} send txn proofs,, verifier time = {:?}, batch verifier time {:?}",
        verifier_time, batch_verifier_time
    );

    let clock = Instant::now();

    let mut even_tuples = Vec::with_capacity(batch_size);
    let mut odd_tuples = Vec::with_capacity(batch_size);

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    for i in 0..batch_size {
        let (even, odd) = proofs[i]
            .verify_and_return_tuples(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                Some(&mut rmc_0),
            )
            .unwrap();
        even_tuples.push(even);
        odd_tuples.push(odd);
    }

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
    let batch_verifier_rmc_time = clock.elapsed();

    println!(
        "For {batch_size} send txn proofs, batch verifier_rmc time {:?}",
        batch_verifier_rmc_time
    );
}

#[cfg(NEVER)]
fn combined_send_txn_proofs() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 16; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 10;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);
    let mut leg_enc_rands = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let ((sk_s, pk_s), (_, pk_s_e)) = &all_keys[i].0;
        let ((_, pk_r), (_, pk_r_e)) = &all_keys[i].1;
        let ((_, _), (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);

        // Create sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s.clone(), id);
        account.balance = 200; // Ensure sufficient balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(3),
    );

    for i in 0..batch_size {
        let updated_account = accounts[i].get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

        updated_accounts.push(updated_account);
        updated_account_comms.push(updated_account_comm);
        paths.push(path);
    }

    let root = account_tree.root_node();

    let nonces: Vec<Vec<u8>> = (0..batch_size)
        .map(|i| format!("combined_send_nonce_{}", i).into_bytes())
        .collect();

    let clock = Instant::now();
    let (mut even_prover, mut odd_prover) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let mut proofs = Vec::with_capacity(batch_size);
    let mut nullifiers = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let (proof, nullifier) = AffirmAsSenderTxnProof::new_with_given_prover(
            &mut rng,
            amount,
            leg_encs[i].clone(),
            leg_enc_rands[i].clone(),
            &accounts[i],
            &updated_accounts[i],
            updated_account_comms[i],
            paths[i].clone(),
            &root,
            &nonces[i],
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )
        .unwrap();
        proofs.push(proof);
        nullifiers.push(nullifier);
    }

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let proving_time = clock.elapsed();

    let clock = Instant::now();
    let (mut even_verifier, mut odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                None,
            )
            .unwrap();
    }

    verify_with_rng(
        even_verifier,
        odd_verifier,
        &even_bp,
        &odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let verification_time = clock.elapsed();

    let clock = Instant::now();
    let (mut even_verifier, mut odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();
    }

    let (even_tuple_rmc, odd_tuple_rmc) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();
    let rmc_verification_time = clock.elapsed();

    println!("Combined send proving time = {:?}", proving_time);
    println!("Combined send verification time = {:?}", verification_time);
    println!(
        "Combined send RMC verification time = {:?}",
        rmc_verification_time
    );
    println!(
        "Combined send proof size = {} bytes",
        even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
    );
}

#[cfg(NEVER)]
fn combined_create_and_send() {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 16;
    const L: usize = 512;
    let (
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_asset_and_account_params::<NUM_GENS>();

    let asset_id = 1;
    let amount = 100;

    let (((sk_s, pk_s), (_, pk_s_e)), ((_, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let role = false;
    let keys = vec![(role, pk_a_e.0)];
    let asset_data = AssetData::new(
        asset_id,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.sl_params.delta,
    )
    .unwrap();

    let set = vec![asset_data.commitment];
    let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
        &set,
        &asset_tree_params,
        Some(3),
    );
    let asset_path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    let (leg, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        role,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
    account.balance = 200;

    let account_tree = tests_new_ct::get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        4,
    )
    .unwrap();
    let account_tree_root = account_tree.root_node();

    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let account_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let nonce = b"test_nonce";

    let clock = Instant::now();

    let (mut even_prover, mut odd_prover) = tests_new_ct::create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let leg_creation_proof = LegCreationProof::new_with_given_prover(
        &mut rng,
        leg.clone(),
        leg_enc.clone(),
        leg_enc_rand.clone(),
        asset_path.clone(),
        asset_data,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover,
        &mut odd_prover,
    )
    .unwrap();

    let (send_proof, nullifier) = AffirmAsSenderTxnProof::new_with_given_prover(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &account,
        &updated_account,
        updated_account_comm,
        account_path.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut odd_prover,
        &mut even_prover,
    )
    .unwrap();

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let proving_time = clock.elapsed();

    let clock = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    send_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.clone(),
            &account_tree_root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        even_verifier,
        odd_verifier,
        &even_bp,
        &odd_bp,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let verification_time = clock.elapsed();

    let clock = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    send_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.clone(),
            &account_tree_root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let rmc_verification_time = clock.elapsed();

    println!(
        "proving time = {:?}, verification time = {:?}, rmc verification time = {:?}",
        proving_time, verification_time, rmc_verification_time
    );
    println!(
        "Combined create and send proof size = {} bytes",
        leg_enc.compressed_size()
            + leg_creation_proof.compressed_size()
            + send_proof.compressed_size()
            + even_bp.compressed_size()
            + odd_bp.compressed_size()
    );
}

#[cfg(NEVER)]
fn batch_receive_txn_proofs() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 5;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);
    let mut leg_enc_rands = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let ((_, pk_s), (_, pk_s_e)) = &all_keys[i].0;
        let ((sk_r, pk_r), (_, pk_r_e)) = &all_keys[i].1;
        let ((_, _), (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);

        // Create receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r.clone(), id);
        account.balance = 200; // Ensure some initial balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(3),
    );

    for i in 0..batch_size {
        let updated_account = accounts[i].get_state_for_receive();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

        updated_accounts.push(updated_account);
        updated_account_comms.push(updated_account_comm);
        paths.push(path);
    }

    let root = account_tree.root_node();

    let nonces: Vec<Vec<u8>> = (0..batch_size)
        .map(|i| format!("batch_receive_nonce_{}", i).into_bytes())
        .collect();

    let mut proofs = Vec::with_capacity(batch_size);
    let mut nullifiers = Vec::with_capacity(batch_size);

    for i in 0..batch_size {
        let (proof, nullifier) = AffirmAsReceiverTxnProof::new(
            &mut rng,
            leg_encs[i].clone(),
            leg_enc_rands[i].clone(),
            &accounts[i],
            &updated_accounts[i],
            updated_account_comms[i],
            paths[i].clone(),
            &root,
            &nonces[i],
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        proofs.push(proof);
        nullifiers.push(nullifier);
    }

    let clock = Instant::now();

    for i in 0..batch_size {
        proofs[i]
            .verify(
                &mut rng,
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
    }

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut even_tuples = Vec::with_capacity(batch_size);
    let mut odd_tuples = Vec::with_capacity(batch_size);

    // These can also be done in parallel
    for i in 0..batch_size {
        let (even, odd) = proofs[i]
            .verify_and_return_tuples(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();
        even_tuples.push(even);
        odd_tuples.push(odd);
    }

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let batch_verifier_time = clock.elapsed();

    println!(
        "For {batch_size} receive txn proofs, verifier time = {:?}, batch verifier time {:?}",
        verifier_time, batch_verifier_time
    );

    let clock = Instant::now();

    let mut even_tuples = Vec::with_capacity(batch_size);
    let mut odd_tuples = Vec::with_capacity(batch_size);

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    for i in 0..batch_size {
        let (even, odd) = proofs[i]
            .verify_and_return_tuples(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                Some(&mut rmc_0),
            )
            .unwrap();
        even_tuples.push(even);
        odd_tuples.push(odd);
    }

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
    let batch_verifier_rmc_time = clock.elapsed();

    println!(
        "For {batch_size} receive txn proofs, batch verifier_rmc time {:?}",
        batch_verifier_rmc_time
    );
}

#[cfg(NEVER)]
fn combined_receive_txn_proofs() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 15;
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 5;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);
    let mut leg_enc_rands = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let ((_, pk_s), (_, pk_s_e)) = &all_keys[i].0;
        let ((sk_r, pk_r), (_, pk_r_e)) = &all_keys[i].1;
        let ((_, _), (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);

        // Create receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r.clone(), id);
        account.balance = 200; // Ensure some initial balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(3),
    );

    for i in 0..batch_size {
        let updated_account = accounts[i].get_state_for_receive();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

        updated_accounts.push(updated_account);
        updated_account_comms.push(updated_account_comm);
        paths.push(path);
    }

    let root = account_tree.root_node();

    let nonces: Vec<Vec<u8>> = (0..batch_size)
        .map(|i| format!("combined_receive_nonce_{}", i).into_bytes())
        .collect();

    let clock = Instant::now();
    let (mut even_prover, mut odd_prover) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let mut proofs = Vec::with_capacity(batch_size);
    let mut nullifiers = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let (proof, nullifier) = AffirmAsReceiverTxnProof::new_with_given_prover(
            &mut rng,
            leg_encs[i].clone(),
            leg_enc_rands[i].clone(),
            &accounts[i],
            &updated_accounts[i],
            updated_account_comms[i],
            paths[i].clone(),
            &root,
            &nonces[i],
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )
        .unwrap();
        proofs.push(proof);
        nullifiers.push(nullifier);
    }

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let proving_time = clock.elapsed();

    let clock = Instant::now();
    let (mut even_verifier, mut odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                None,
            )
            .unwrap();
    }

    verify_with_rng(
        even_verifier,
        odd_verifier,
        &even_bp,
        &odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let verification_time = clock.elapsed();

    let clock = Instant::now();
    let (mut even_verifier, mut odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_encs[i].clone(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();
    }

    let (even_tuple_rmc, odd_tuple_rmc) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();
    let rmc_verification_time = clock.elapsed();

    println!("Combined receive proving time = {:?}", proving_time);
    println!(
        "Combined receive verification time = {:?}",
        verification_time
    );
    println!(
        "Combined receive RMC verification time = {:?}",
        rmc_verification_time
    );
    println!(
        "Combined receive proof size = {} bytes",
        even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
    );
}

#[cfg(NEVER)]
fn single_shot_settlement() {
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 512;

    let asset_tree_height = 3;
    let account_tree_height = 4;

    let (
        asset_data,
        asset_path,
        asset_tree_root,
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        receiver_account,
        updated_sender_account,
        updated_receiver_account,
        updated_sender_account_comm,
        updated_receiver_account_comm,
        sender_path,
        receiver_path,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_single_leg_settlement::<NUM_GENS, L>(asset_tree_height, account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"single_shot_settlement_nonce_txn_id_1";

    println!(
        "For L={L}, asset tree height = {asset_tree_height}, account tree height = {account_tree_height}"
    );

    // Create all three proofs
    let start = Instant::now();
    let settlement_proof = LegCreationProof::new(
        &mut rng,
        leg.clone(),
        leg_enc.clone(),
        leg_enc_rand.clone(),
        asset_path.clone(),
        asset_data,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    println!("Settlement creation time : {:?}", start.elapsed());

    let start = Instant::now();
    let (sender_proof, sender_nullifier) = IrreversibleAffirmAsSenderTxnProof::new(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &sender_account,
        &updated_sender_account,
        updated_sender_account_comm,
        sender_path.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    println!("Sender time : {:?}", start.elapsed());

    let start = Instant::now();
    let (receiver_proof, receiver_nullifier) = IrreversibleAffirmAsReceiverTxnProof::new(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &receiver_account,
        &updated_receiver_account,
        updated_receiver_account_comm,
        receiver_path.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    println!("Receiver time : {:?}", start.elapsed());

    let start = Instant::now();

    // All 3 can be verified in parallel
    let (settlement_even, settlement_odd) = settlement_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    println!("tuples time : {:?}", start.elapsed());
    println!(
        "tuples count {} {} {} {}",
        settlement_odd.proof_dependent_points.len()
            + sender_even.proof_dependent_points.len()
            + receiver_even.proof_dependent_points.len(),
        settlement_odd.proof_independent_scalars.len()
            + sender_odd.proof_independent_scalars.len()
            + receiver_even.proof_independent_scalars.len(),
        settlement_even.proof_dependent_points.len()
            + sender_odd.proof_dependent_points.len()
            + receiver_odd.proof_dependent_points.len(),
        settlement_even.proof_independent_scalars.len()
            + sender_odd.proof_independent_scalars.len()
            + receiver_odd.proof_independent_scalars.len(),
    );

    // Asset tree uses opposite curves than account tree so merging accordingly
    let even_tuples = vec![settlement_odd, sender_even, receiver_even];
    let odd_tuples = vec![settlement_even, sender_odd, receiver_odd];

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let verifier_time = start.elapsed();

    let start = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (settlement_even, settlement_odd) = settlement_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_0),
        )
        .unwrap();

    // Asset tree uses opposite curves than account tree so merging accordingly
    let even_tuples = vec![settlement_odd, sender_even, receiver_even];
    let odd_tuples = vec![settlement_even, sender_odd, receiver_odd];

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
    let verifier_rmc_time = start.elapsed();

    println!(
        "proof size = {}, verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        settlement_proof.compressed_size()
            + leg_enc.compressed_size()
            + receiver_proof.compressed_size()
            + sender_proof.compressed_size(),
        verifier_time,
        verifier_rmc_time
    );
}

#[cfg(NEVER)]
fn swap_settlement() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 512;
    let (
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_asset_and_account_params::<NUM_GENS>();

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (sk_m_e, pk_m_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_tree_height = 3;
    let account_tree_height = 4;

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Both assets have same mediator
    let role = false;
    let keys = vec![(role, pk_m_e.0)];
    let asset_data_1 = AssetData::new(
        asset_id_1,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.sl_params.delta,
    )
    .unwrap();
    let asset_data_2 = AssetData::new(
        asset_id_2,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.sl_params.delta,
    )
    .unwrap();

    let set = vec![asset_data_1.commitment, asset_data_2.commitment];
    let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
        &set,
        &asset_tree_params,
        Some(asset_tree_height),
    );
    let asset_path_1 = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_path_2 = asset_tree.get_path_to_leaf_for_proof(1, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    // Create two legs for swap
    let (leg_1, leg_enc_1, leg_enc_rand_1) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_m_e.0,
        role,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );
    let (leg_2, leg_enc_2, leg_enc_rand_2) = tests_new_ct::setup_leg(
        &mut rng,
        pk_r.0,
        pk_s.0,
        pk_m_e.0,
        role,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_s.clone(), alice_id);
    alice_account_1.balance = 200;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_s.clone(), alice_id);
    alice_account_2.balance = 50;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_r.clone(), bob_id);
    bob_account_1.balance = 50;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_r, bob_id);
    bob_account_2.balance = 300;
    let bob_account_comm_2 = bob_account_2.commit(account_comm_key.clone()).unwrap();

    // Account tree for all four accounts
    let account_comms = vec![
        alice_account_comm_1.0,
        alice_account_comm_2.0,
        bob_account_comm_1.0,
        bob_account_comm_2.0,
    ];
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &account_comms,
        &account_tree_params,
        Some(account_tree_height),
    );
    let account_tree_root = account_tree.root_node();

    // Prepare updated account states
    let updated_alice_account_1 = alice_account_1.get_state_for_send(amount_1).unwrap();
    let updated_alice_account_comm_1 = updated_alice_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_alice_account_2 = alice_account_2.get_state_for_receive();
    let updated_alice_account_comm_2 = updated_alice_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    let updated_bob_account_1 = bob_account_1.get_state_for_receive();
    let updated_bob_account_comm_1 = updated_bob_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0).unwrap();

    let updated_bob_account_2 = bob_account_2.get_state_for_send(amount_2).unwrap();
    let updated_bob_account_comm_2 = updated_bob_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0).unwrap();

    let nonce = b"swap_settlement_nonce_txn_id_1";

    // Combined settlement proofs for both legs
    let clock = Instant::now();
    let (mut even_prover_settlement, mut odd_prover_settlement) = tests_new_ct::create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof_1 = LegCreationProof::new_with_given_prover(
        &mut rng,
        leg_1.clone(),
        leg_enc_1.clone(),
        leg_enc_rand_1.clone(),
        asset_path_1.clone(),
        asset_data_1,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover_settlement,
        &mut odd_prover_settlement,
    )
    .unwrap();

    let settlement_proof_2 = LegCreationProof::new_with_given_prover(
        &mut rng,
        leg_2.clone(),
        leg_enc_2.clone(),
        leg_enc_rand_2.clone(),
        asset_path_2.clone(),
        asset_data_2,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover_settlement,
        &mut odd_prover_settlement,
    )
    .unwrap();

    let (settlement_even_bp, settlement_odd_bp) = prove_with_rng(
        even_prover_settlement,
        odd_prover_settlement,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let settlement_proving_time = clock.elapsed();

    // Verify settlement proofs (both legs)
    let clock = Instant::now();

    let (mut settlement_even_verifier, mut settlement_odd_verifier) =
        tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
            LEG_TXN_EVEN_LABEL,
            LEG_TXN_ODD_LABEL,
        );

    settlement_proof_1
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_1.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            None,
        )
        .unwrap();

    settlement_proof_2
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_2.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        settlement_even_verifier,
        settlement_odd_verifier,
        &settlement_even_bp,
        &settlement_odd_bp,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let settlement_verification_time = clock.elapsed();

    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    // Verify settlement proofs (both legs)
    let clock = Instant::now();

    let (mut settlement_even_verifier, mut settlement_odd_verifier) =
        tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
            LEG_TXN_EVEN_LABEL,
            LEG_TXN_ODD_LABEL,
        );

    settlement_proof_1
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_1.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    settlement_proof_2
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_2.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
        settlement_even_verifier,
        settlement_odd_verifier,
        &settlement_even_bp,
        &settlement_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rmc_1,
        &mut rmc_0,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let settlement_verification_time_rmc = clock.elapsed();

    // Mediator affirms both legs with a single proof
    let clock = Instant::now();
    let accept = true;
    // Mediator is at index 0 in both assets
    let index_in_asset_data = 0;

    // This could be made a bit faster and shorter if prover was willing to prove that same secret
    // key is used. But this might not be the setting in practice.

    // Create shared transcript for mediator proof covering both legs
    let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

    let med_proof_1 = MediatorTxnProof::new_with_given_transcript(
        &mut rng,
        leg_enc_1.clone(),
        asset_id_1,
        sk_m_e.0,
        accept,
        index_in_asset_data,
        nonce,
        enc_gen,
        &mut transcript,
    )
    .unwrap();

    let med_proof_2 = MediatorTxnProof::new_with_given_transcript(
        &mut rng,
        leg_enc_2.clone(),
        asset_id_2,
        sk_m_e.0,
        accept,
        index_in_asset_data,
        nonce,
        enc_gen,
        &mut transcript,
    )
    .unwrap();

    let mediator_proving_time = clock.elapsed();

    let clock = Instant::now();
    let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

    med_proof_1
        .verify_with_given_transcript(
            leg_enc_1.clone(),
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
            None,
        )
        .unwrap();

    med_proof_2
        .verify_with_given_transcript(
            leg_enc_2.clone(),
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
            None,
        )
        .unwrap();

    let mediator_verification_time = clock.elapsed();

    let clock = Instant::now();
    let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
    let mut rmc_med = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    med_proof_1
        .verify_with_given_transcript(
            leg_enc_1.clone(),
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
            Some(&mut rmc_med),
        )
        .unwrap();

    med_proof_2
        .verify_with_given_transcript(
            leg_enc_2.clone(),
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
            Some(&mut rmc_med),
        )
        .unwrap();

    assert!(rmc_med.verify());

    let mediator_verification_time_rmc = clock.elapsed();

    // Combined alice proofs for both legs (alice sends in leg1, receives in leg2)
    let clock = Instant::now();
    let (mut even_prover_alice, mut odd_prover_alice) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Alice proof for leg1 (sending asset1)
    let (alice_proof_leg1, alice_nullifier_leg1) = AffirmAsSenderTxnProof::new_with_given_prover(
        &mut rng,
        amount_1,
        leg_enc_1.clone(),
        leg_enc_rand_1.clone(),
        &alice_account_1,
        &updated_alice_account_1,
        updated_alice_account_comm_1,
        alice_path_1.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_alice,
        &mut odd_prover_alice,
    )
    .unwrap();

    // Alice proof for leg2 (receiving asset2)
    let (alice_proof_leg2, alice_nullifier_leg2) = AffirmAsReceiverTxnProof::new_with_given_prover(
        &mut rng,
        leg_enc_2.clone(),
        leg_enc_rand_2.clone(),
        &alice_account_2,
        &updated_alice_account_2,
        updated_alice_account_comm_2,
        alice_path_2.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_alice,
        &mut odd_prover_alice,
    )
    .unwrap();

    let (alice_even_bp, alice_odd_bp) = prove_with_rng(
        even_prover_alice,
        odd_prover_alice,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let alice_proving_time = clock.elapsed();

    // Combined bob proofs for both legs (bob receives leg1, sends leg2)
    let clock = Instant::now();
    let (mut even_prover_bob, mut odd_prover_bob) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Bob proof for leg1 (receiving asset1)
    let (bob_proof_leg1, bob_nullifier_leg1) = AffirmAsReceiverTxnProof::new_with_given_prover(
        &mut rng,
        leg_enc_1.clone(),
        leg_enc_rand_1.clone(),
        &bob_account_1,
        &updated_bob_account_1,
        updated_bob_account_comm_1,
        bob_path_1.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_bob,
        &mut odd_prover_bob,
    )
    .unwrap();

    // Bob proof for leg2 (sending asset2)
    let (bob_proof_leg2, bob_nullifier_leg2) = AffirmAsSenderTxnProof::new_with_given_prover(
        &mut rng,
        amount_2,
        leg_enc_2.clone(),
        leg_enc_rand_2.clone(),
        &bob_account_2,
        &updated_bob_account_2,
        updated_bob_account_comm_2,
        bob_path_2.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_bob,
        &mut odd_prover_bob,
    )
    .unwrap();

    let (bob_even_bp, bob_odd_bp) = prove_with_rng(
        even_prover_bob,
        odd_prover_bob,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let bob_proving_time = clock.elapsed();

    // Verify alice proofs (both legs)
    let clock = Instant::now();
    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let alice_verification_time = clock.elapsed();

    // Verify bob proofs (both legs)
    let clock = Instant::now();
    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let bob_verification_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let alice_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let bob_verification_time_rmc = clock.elapsed();

    // Counter update proofs
    // Alice: ClaimReceivedTxnProof for alice_account_2 (receiving leg2), SenderCounterUpdateTxnProof for alice_account_1 (sending leg1)
    // Bob: ClaimReceivedTxnProof for bob_account_1 (receiving leg1), SenderCounterUpdateTxnProof for bob_account_2 (sending leg2)

    // Alice updates
    let updated_alice_account_3 = updated_alice_account_2
        .get_state_for_claiming_received(amount_2)
        .unwrap();
    let updated_alice_account_comm_3 = updated_alice_account_3
        .commit(account_comm_key.clone())
        .unwrap();

    let updated_alice_account_4 = updated_alice_account_1
        .get_state_for_decreasing_counter(None)
        .unwrap();
    let updated_alice_account_comm_4 = updated_alice_account_4
        .commit(account_comm_key.clone())
        .unwrap();

    // Bob updates
    let updated_bob_account_3 = updated_bob_account_1
        .get_state_for_claiming_received(amount_1)
        .unwrap();
    let updated_bob_account_comm_3 = updated_bob_account_3
        .commit(account_comm_key.clone())
        .unwrap();

    let updated_bob_account_4 = updated_bob_account_2
        .get_state_for_decreasing_counter(None)
        .unwrap();
    let updated_bob_account_comm_4 = updated_bob_account_4
        .commit(account_comm_key.clone())
        .unwrap();

    // In practice, existing tree will be updated
    let account_comms = vec![
        alice_account_comm_1.0,
        alice_account_comm_2.0,
        bob_account_comm_1.0,
        bob_account_comm_2.0,
        updated_alice_account_comm_1.0,
        updated_alice_account_comm_2.0,
        updated_bob_account_comm_1.0,
        updated_bob_account_comm_2.0,
    ];
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &account_comms,
        &account_tree_params,
        Some(4),
    );
    let account_tree_root = account_tree.root_node();

    let alice_1_path = account_tree.get_path_to_leaf_for_proof(4, 0).unwrap();
    let alice_2_path = account_tree.get_path_to_leaf_for_proof(5, 0).unwrap();
    let bob_1_path = account_tree.get_path_to_leaf_for_proof(6, 0).unwrap();
    let bob_2_path = account_tree.get_path_to_leaf_for_proof(7, 0).unwrap();

    // Counter update proofs
    // Alice counter update proving
    let clock = Instant::now();

    // Alice counter updates with her own provers
    let (mut even_prover_alice, mut odd_prover_alice) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (alice_counter_update_proof, alice_cu_nullifier) =
        SenderCounterUpdateTxnProof::new_with_given_prover(
            &mut rng,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            &updated_alice_account_1,
            &updated_alice_account_4,
            updated_alice_account_comm_4,
            alice_1_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    let (alice_claim_proof, alice_claim_nullifier) = ClaimReceivedTxnProof::new_with_given_prover(
        &mut rng,
        amount_2,
        leg_enc_2.clone(),
        leg_enc_rand_2.clone(),
        &updated_alice_account_2,
        &updated_alice_account_3,
        updated_alice_account_comm_3,
        alice_2_path,
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_alice,
        &mut odd_prover_alice,
    )
    .unwrap();

    let (alice_even_bp, alice_odd_bp) = prove_with_rng(
        even_prover_alice,
        odd_prover_alice,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let alice_counter_update_proving_time = clock.elapsed();

    // Bob counter update proving
    let clock = Instant::now();

    // Bob counter updates with his own provers
    let (mut even_prover_bob, mut odd_prover_bob) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (bob_claim_proof, bob_claim_nullifier) = ClaimReceivedTxnProof::new_with_given_prover(
        &mut rng,
        amount_1,
        leg_enc_1.clone(),
        leg_enc_rand_1.clone(),
        &updated_bob_account_1,
        &updated_bob_account_3,
        updated_bob_account_comm_3,
        bob_1_path,
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_bob,
        &mut odd_prover_bob,
    )
    .unwrap();

    let (bob_counter_update_proof, bob_cu_nullifier) =
        SenderCounterUpdateTxnProof::new_with_given_prover(
            &mut rng,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            &updated_bob_account_2,
            &updated_bob_account_4,
            updated_bob_account_comm_4,
            bob_2_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    let (bob_even_bp, bob_odd_bp) = prove_with_rng(
        even_prover_bob,
        odd_prover_bob,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let bob_counter_update_proving_time = clock.elapsed();

    // Verify counter update proofs
    // Alice counter update verification
    let clock = Instant::now();

    // Verify Alice counter update proofs
    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_4,
            alice_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_3,
            alice_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let alice_counter_update_verification_time = clock.elapsed();

    // Bob counter update verification
    let clock = Instant::now();

    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    // Verify Bob counter update proofs
    bob_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_3,
            bob_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_4,
            bob_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let bob_counter_update_verification_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_4,
            alice_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    alice_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_3,
            alice_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let alice_counter_update_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    // Verify Bob counter update proofs
    bob_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_3,
            bob_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    bob_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_4,
            bob_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let bob_counter_update_verification_time_rmc = clock.elapsed();

    let settlement_proof_size = settlement_even_bp.compressed_size()
        + settlement_odd_bp.compressed_size()
        + settlement_proof_1.compressed_size()
        + settlement_proof_2.compressed_size();
    let mediator_proof_size = med_proof_1.compressed_size() + med_proof_2.compressed_size();
    let alice_affirmation_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_proof_leg1.compressed_size()
        + alice_proof_leg2.compressed_size();
    let alice_counter_update_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_claim_proof.compressed_size()
        + alice_counter_update_proof.compressed_size();
    let bob_affirmation_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_proof_leg1.compressed_size()
        + bob_proof_leg2.compressed_size();
    let bob_counter_update_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_claim_proof.compressed_size()
        + bob_counter_update_proof.compressed_size();

    println!(
        "For L={L}, asset tree height={asset_tree_height}, account tree height={account_tree_height}"
    );

    println!(
        "Settlement proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        settlement_proving_time,
        settlement_verification_time,
        settlement_verification_time_rmc,
        settlement_proof_size
    );
    println!(
        "Mediator affirmation proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        mediator_proving_time,
        mediator_verification_time,
        mediator_verification_time_rmc,
        mediator_proof_size
    );
    println!(
        "Alice affirmation proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        alice_proving_time,
        alice_verification_time,
        alice_verification_time_rmc,
        alice_affirmation_proof_size
    );
    println!(
        "Alice counter update proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        alice_counter_update_proving_time,
        alice_counter_update_verification_time,
        alice_counter_update_verification_time_rmc,
        alice_counter_update_proof_size
    );
    println!(
        "Bob affirmation proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        bob_proving_time,
        bob_verification_time,
        bob_verification_time_rmc,
        bob_affirmation_proof_size
    );
    println!(
        "Bob counter update proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        bob_counter_update_proving_time,
        bob_counter_update_verification_time,
        bob_counter_update_verification_time_rmc,
        bob_counter_update_proof_size
    );
}

#[cfg(NEVER)]
fn reverse_settlement() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 2;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Create two legs for swap
    let (_, leg_enc_1, leg_enc_rand_1) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );
    let (_, leg_enc_2, leg_enc_rand_2) = tests_new_ct::setup_leg(
        &mut rng,
        pk_r.0,
        pk_s.0,
        pk_a_e.0,
        true,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_s.clone(), alice_id);
    alice_account_1.balance = 500;
    alice_account_1.counter = 1;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_s.clone(), alice_id);
    alice_account_2.balance = 50;
    alice_account_2.counter = 1;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_r.clone(), bob_id);
    bob_account_1.balance = 500;
    bob_account_1.counter = 1;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_r.clone(), bob_id);
    bob_account_2.balance = 50;
    bob_account_2.counter = 1;
    let bob_account_comm_2 = bob_account_2.commit(account_comm_key.clone()).unwrap();

    // Account tree for all four accounts
    let account_comms = vec![
        alice_account_comm_1.0,
        alice_account_comm_2.0,
        bob_account_comm_1.0,
        bob_account_comm_2.0,
    ];
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &account_comms,
        &account_tree_params,
        Some(4),
    );
    let account_tree_root = account_tree.root_node();

    // Prepare updated account states
    let updated_alice_account_1 = alice_account_1
        .get_state_for_reversing_send(amount_1)
        .unwrap();
    let updated_alice_account_comm_1 = updated_alice_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_alice_account_2 = alice_account_2
        .get_state_for_decreasing_counter(None)
        .unwrap();
    let updated_alice_account_comm_2 = updated_alice_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    let updated_bob_account_1 = bob_account_1
        .get_state_for_decreasing_counter(None)
        .unwrap();
    let updated_bob_account_comm_1 = updated_bob_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0).unwrap();

    let updated_bob_account_2 = bob_account_2
        .get_state_for_reversing_send(amount_2)
        .unwrap();
    let updated_bob_account_comm_2 = updated_bob_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0).unwrap();

    let nonce = b"reverse_settlement_nonce_txn_id_1";

    // Combined alice proofs for both legs (alice reverses send in leg1, reverses receive in leg2)
    let clock = Instant::now();
    let (mut even_prover_alice, mut odd_prover_alice) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Alice proof for leg1 (reverse sending asset1)
    let (alice_proof_leg1, alice_nullifier_leg1) = SenderReverseTxnProof::new_with_given_prover(
        &mut rng,
        amount_1,
        leg_enc_1.clone(),
        leg_enc_rand_1.clone(),
        &alice_account_1,
        &updated_alice_account_1,
        updated_alice_account_comm_1,
        alice_path_1.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_alice,
        &mut odd_prover_alice,
    )
    .unwrap();

    // Alice proof for leg2 (reverse receiving asset2)
    let (alice_proof_leg2, alice_nullifier_leg2) =
        ReceiverCounterUpdateTxnProof::new_with_given_prover(
            &mut rng,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            &alice_account_2,
            &updated_alice_account_2,
            updated_alice_account_comm_2,
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    let (alice_even_bp, alice_odd_bp) = prove_with_rng(
        even_prover_alice,
        odd_prover_alice,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let alice_proving_time = clock.elapsed();

    // Combined bob proofs for both legs (bob reverses receive in leg1, reverses send in leg2)
    let clock = Instant::now();
    let (mut even_prover_bob, mut odd_prover_bob) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Bob proof for leg1 (reverse receiving asset1)
    let (bob_proof_leg1, bob_nullifier_leg1) =
        ReceiverCounterUpdateTxnProof::new_with_given_prover(
            &mut rng,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            &bob_account_1,
            &updated_bob_account_1,
            updated_bob_account_comm_1,
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    // Bob proof for leg2 (reverse sending asset2)
    let (bob_proof_leg2, bob_nullifier_leg2) = SenderReverseTxnProof::new_with_given_prover(
        &mut rng,
        amount_2,
        leg_enc_2.clone(),
        leg_enc_rand_2.clone(),
        &bob_account_2,
        &updated_bob_account_2,
        updated_bob_account_comm_2,
        bob_path_2.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut even_prover_bob,
        &mut odd_prover_bob,
    )
    .unwrap();

    let (bob_even_bp, bob_odd_bp) = prove_with_rng(
        even_prover_bob,
        odd_prover_bob,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let bob_proving_time = clock.elapsed();

    // Verify alice proofs (both legs)
    let clock = Instant::now();
    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let alice_verification_time = clock.elapsed();

    // Verify bob proofs (both legs)
    let clock = Instant::now();
    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    verify_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let bob_verification_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let alice_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![even_tuple_rmc],
        vec![odd_tuple_rmc],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let bob_verification_time_rmc = clock.elapsed();

    let alice_affirmation_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_proof_leg1.compressed_size()
        + alice_proof_leg2.compressed_size();

    let bob_affirmation_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_proof_leg1.compressed_size()
        + bob_proof_leg2.compressed_size();

    println!(
        "Alice reversing proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        alice_proving_time,
        alice_verification_time,
        alice_verification_time_rmc,
        alice_affirmation_proof_size
    );
    println!(
        "Bob reversing proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
        bob_proving_time,
        bob_verification_time,
        bob_verification_time_rmc,
        bob_affirmation_proof_size
    );
}

#[cfg(NEVER)]
fn single_shot_swap() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 512;
    let (
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_asset_and_account_params::<NUM_GENS>();

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    let keys = vec![(true, pk_a_e.0)];
    let asset_data_1 = AssetData::new(
        asset_id_1,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.sl_params.delta,
    )
    .unwrap();
    let asset_data_2 = AssetData::new(
        asset_id_2,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.sl_params.delta,
    )
    .unwrap();

    let set = vec![asset_data_1.commitment, asset_data_2.commitment];
    let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
        &set,
        &asset_tree_params,
        Some(2),
    );
    let asset_path_1 = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_path_2 = asset_tree.get_path_to_leaf_for_proof(1, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    // Create two legs for swap
    let (leg_1, leg_enc_1, leg_enc_rand_1) = tests_new_ct::setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
        true,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );
    let (leg_2, leg_enc_2, leg_enc_rand_2) = tests_new_ct::setup_leg(
        &mut rng,
        pk_r.0,
        pk_s.0,
        pk_a_e.0,
        true,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        enc_key_gen,
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_s.clone(), alice_id);
    alice_account_1.balance = 200;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_s.clone(), alice_id);
    alice_account_2.balance = 50;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_r.clone(), bob_id);
    bob_account_1.balance = 50;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_r.clone(), bob_id);
    bob_account_2.balance = 300;
    let bob_account_comm_2 = bob_account_2.commit(account_comm_key.clone()).unwrap();

    // Account tree for all four accounts
    let account_comms = vec![
        alice_account_comm_1.0,
        alice_account_comm_2.0,
        bob_account_comm_1.0,
        bob_account_comm_2.0,
    ];
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &account_comms,
        &account_tree_params,
        Some(4),
    );
    let account_tree_root = account_tree.root_node();

    // Prepare updated account states for irreversible swap (no counter changes)
    let updated_alice_account_1 = alice_account_1
        .get_state_for_irreversible_send(amount_1)
        .unwrap();
    assert_eq!(
        updated_alice_account_1.balance,
        alice_account_1.balance - amount_1
    );
    assert_eq!(updated_alice_account_1.counter, alice_account_1.counter);
    let updated_alice_account_comm_1 = updated_alice_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_alice_account_2 = alice_account_2
        .get_state_for_irreversible_receive(amount_2)
        .unwrap();
    assert_eq!(
        updated_alice_account_2.balance,
        alice_account_2.balance + amount_2
    );
    assert_eq!(updated_alice_account_2.counter, alice_account_2.counter);
    let updated_alice_account_comm_2 = updated_alice_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    let updated_bob_account_1 = bob_account_1
        .get_state_for_irreversible_receive(amount_1)
        .unwrap();
    assert_eq!(
        updated_bob_account_1.balance,
        bob_account_1.balance + amount_1
    );
    assert_eq!(updated_bob_account_1.counter, bob_account_1.counter);
    let updated_bob_account_comm_1 = updated_bob_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0).unwrap();

    let updated_bob_account_2 = bob_account_2
        .get_state_for_irreversible_send(amount_2)
        .unwrap();
    assert_eq!(
        updated_bob_account_2.balance,
        bob_account_2.balance - amount_2
    );
    assert_eq!(updated_bob_account_2.counter, bob_account_2.counter);
    let updated_bob_account_comm_2 = updated_bob_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0).unwrap();

    let nonce = b"single_shot_swap_nonce_txn_id_1";

    // Combined settlement proofs for both legs
    let (mut even_prover_settlement, mut odd_prover_settlement) = tests_new_ct::create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof_1 = LegCreationProof::new_with_given_prover(
        &mut rng,
        leg_1.clone(),
        leg_enc_1.clone(),
        leg_enc_rand_1.clone(),
        asset_path_1.clone(),
        asset_data_1,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover_settlement,
        &mut odd_prover_settlement,
    )
    .unwrap();

    let settlement_proof_2 = LegCreationProof::new_with_given_prover(
        &mut rng,
        leg_2.clone(),
        leg_enc_2.clone(),
        leg_enc_rand_2.clone(),
        asset_path_2.clone(),
        asset_data_2,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover_settlement,
        &mut odd_prover_settlement,
    )
    .unwrap();

    let (settlement_even_bp, settlement_odd_bp) = prove_with_rng(
        even_prover_settlement,
        odd_prover_settlement,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    // Combined proofs for Alice (sending in leg1, receiving in leg2)
    let (mut even_prover_alice, mut odd_prover_alice) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (alice_sender_proof, alice_sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover(
            &mut rng,
            amount_1,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            &alice_account_1,
            &updated_alice_account_1,
            updated_alice_account_comm_1,
            alice_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    let (alice_receiver_proof, alice_receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover(
            &mut rng,
            amount_2,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            &alice_account_2,
            &updated_alice_account_2,
            updated_alice_account_comm_2,
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    let (alice_even_bp, alice_odd_bp) = prove_with_rng(
        even_prover_alice,
        odd_prover_alice,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    // Combined proofs for Bob (receiving in leg1, sending in leg2)
    let (mut even_prover_bob, mut odd_prover_bob) = tests_new_ct::create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (bob_receiver_proof, bob_receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover(
            &mut rng,
            amount_1,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            &bob_account_1,
            &updated_bob_account_1,
            updated_bob_account_comm_1,
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    let (bob_sender_proof, bob_sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover(
            &mut rng,
            amount_2,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            &bob_account_2,
            &updated_bob_account_2,
            updated_bob_account_comm_2,
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    let (bob_even_bp, bob_odd_bp) = prove_with_rng(
        even_prover_bob,
        odd_prover_bob,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    // Verify all proofs
    let clock = Instant::now();

    let (mut settlement_even_verifier, mut settlement_odd_verifier) =
        tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
            LEG_TXN_EVEN_LABEL,
            LEG_TXN_ODD_LABEL,
        );

    settlement_proof_1
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_1.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            None,
        )
        .unwrap();

    settlement_proof_2
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_2.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            None,
        )
        .unwrap();

    let (even_tuple_legs, odd_tuple_legs) = get_verification_tuples_with_rng(
        settlement_even_verifier,
        settlement_odd_verifier,
        &settlement_even_bp,
        &settlement_odd_bp,
        &mut rng,
    )
    .unwrap();

    // Verify Alice proofs
    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    let (even_tuple_alice, odd_tuple_alice) = get_verification_tuples_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        &mut rng,
    )
    .unwrap();

    // Verify Bob proofs
    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    let (even_tuple_bob, odd_tuple_bob) = get_verification_tuples_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        &mut rng,
    )
    .unwrap();

    let even_tuples = vec![odd_tuple_legs, even_tuple_alice, even_tuple_bob];
    let odd_tuples = vec![even_tuple_legs, odd_tuple_alice, odd_tuple_bob];

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    let (mut settlement_even_verifier, mut settlement_odd_verifier) =
        tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
            LEG_TXN_EVEN_LABEL,
            LEG_TXN_ODD_LABEL,
        );

    settlement_proof_1
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_1.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    settlement_proof_2
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_2.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_legs, odd_tuple_legs) = get_verification_tuples_with_rng(
        settlement_even_verifier,
        settlement_odd_verifier,
        &settlement_even_bp,
        &settlement_odd_bp,
        &mut rng,
    )
    .unwrap();

    // Verify Alice proofs
    let (mut alice_even_verifier, mut alice_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    alice_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_alice, odd_tuple_alice) = get_verification_tuples_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        &mut rng,
    )
    .unwrap();

    // Verify Bob proofs
    let (mut bob_even_verifier, mut bob_odd_verifier) =
        tests_new_ct::create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.clone(),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    bob_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_2.clone(),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    let (even_tuple_bob, odd_tuple_bob) = get_verification_tuples_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        &mut rng,
    )
    .unwrap();

    add_verification_tuples_batches_to_rmc(
        vec![odd_tuple_legs, even_tuple_alice, even_tuple_bob],
        vec![even_tuple_legs, odd_tuple_alice, odd_tuple_bob],
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();

    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verifier_time_rmc = clock.elapsed();

    println!(
        "verifier time {:?}, verifier time (with RandomizedMultChecker) = {:?}",
        verifier_time, verifier_time_rmc
    );
}

#[cfg(NEVER)]
fn single_shot_combined_create_and_send() {
    const NUM_GENS: usize = 1 << 16;
    const L: usize = 512;

    let asset_tree_height = 3;
    let account_tree_height = 4;

    let (
        asset_data,
        asset_path,
        asset_tree_root,
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        receiver_account,
        updated_sender_account,
        updated_receiver_account,
        updated_sender_account_comm,
        updated_receiver_account_comm,
        sender_path,
        receiver_path,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_single_leg_settlement::<NUM_GENS, L>(asset_tree_height, account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"single_shot_combined_nonce_txn_id_1";

    let start = Instant::now();

    let (mut even_prover, mut odd_prover) = tests_new_ct::create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let leg_creation_proof = LegCreationProof::new_with_given_prover(
        &mut rng,
        leg.clone(),
        leg_enc.clone(),
        leg_enc_rand.clone(),
        asset_path.clone(),
        asset_data,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover,
        &mut odd_prover,
    )
    .unwrap();

    let (sender_proof, sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &sender_account,
            &updated_sender_account,
            updated_sender_account_comm,
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_prover,
            &mut even_prover,
        )
        .unwrap();

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let proving_time = start.elapsed();

    let start = Instant::now();

    let (receiver_proof, receiver_nullifier) = IrreversibleAffirmAsReceiverTxnProof::new(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &receiver_account,
        &updated_receiver_account,
        updated_receiver_account_comm,
        receiver_path.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let receiver_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.clone(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            None,
        )
        .unwrap();

    let (even_tuple, odd_tuple) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let even_tuples = vec![odd_tuple, receiver_even];
    let odd_tuples = vec![even_tuple, receiver_odd];

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let verification_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.clone(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
        )
        .unwrap();

    let even_tuples = vec![odd_tuple_rmc, receiver_even];
    let odd_tuples = vec![even_tuple_rmc, receiver_odd];

    add_verification_tuples_batches_to_rmc(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_1,
        &mut rmc_0,
    )
    .unwrap();

    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let rmc_verification_time = start.elapsed();

    println!(
        "Total proof size = {}",
        even_bp.compressed_size()
            + odd_bp.compressed_size()
            + leg_enc.compressed_size()
            + leg_creation_proof.compressed_size()
            + sender_proof.compressed_size()
            + receiver_proof.compressed_size()
    );
    println!(
        "Combined (settlement + sender): proving time = {:?}",
        proving_time
    );
    println!("Receiver: proving time = {:?}", receiver_proving_time);
    println!(
        "verification time = {:?}, rmc verification time = {:?}",
        verification_time, rmc_verification_time
    );
}

#[cfg(NEVER)]
fn single_shot_combined_create_and_recv() {
    const NUM_GENS: usize = 1 << 14;
    const L: usize = 512;

    let asset_tree_height = 3;
    let account_tree_height = 4;

    let (
        asset_data,
        asset_path,
        asset_tree_root,
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        receiver_account,
        updated_sender_account,
        updated_receiver_account,
        updated_sender_account_comm,
        updated_receiver_account_comm,
        sender_path,
        receiver_path,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_single_leg_settlement::<NUM_GENS, L>(asset_tree_height, account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"single_shot_combined_recv_nonce_txn_id_1";

    let start = Instant::now();

    let (mut even_prover, mut odd_prover) = tests_new_ct::create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let leg_creation_proof = LegCreationProof::new_with_given_prover(
        &mut rng,
        leg.clone(),
        leg_enc.clone(),
        leg_enc_rand.clone(),
        asset_path.clone(),
        asset_data,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover,
        &mut odd_prover,
    )
    .unwrap();

    let (receiver_proof, receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &receiver_account,
            &updated_receiver_account,
            updated_receiver_account_comm,
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_prover,
            &mut even_prover,
        )
        .unwrap();

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let proving_time = start.elapsed();

    let start = Instant::now();

    let (sender_proof, sender_nullifier) = IrreversibleAffirmAsSenderTxnProof::new(
        &mut rng,
        amount,
        leg_enc.clone(),
        leg_enc_rand.clone(),
        &sender_account,
        &updated_sender_account,
        updated_sender_account_comm,
        sender_path.clone(),
        &account_tree_root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    let sender_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.clone(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            None,
        )
        .unwrap();

    let (even_tuple, odd_tuple) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    println!("tuples time : {:?}", start.elapsed());

    println!(
        "tuples count {} {} {} {}",
        odd_tuple.proof_dependent_points.len() + sender_even.proof_dependent_points.len(),
        odd_tuple.proof_independent_scalars.len() + sender_odd.proof_independent_scalars.len(),
        even_tuple.proof_dependent_points.len() + sender_odd.proof_dependent_points.len(),
        even_tuple.proof_independent_scalars.len() + sender_odd.proof_independent_scalars.len(),
    );

    let even_tuples = vec![odd_tuple, sender_even];
    let odd_tuples = vec![even_tuple, sender_odd];

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let verification_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.clone(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
        )
        .unwrap();

    let even_tuples = vec![odd_tuple_rmc, sender_even];
    let odd_tuples = vec![even_tuple_rmc, sender_odd];

    add_verification_tuples_batches_to_rmc(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_1,
        &mut rmc_0,
    )
    .unwrap();

    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let rmc_verification_time = start.elapsed();

    println!(
        "For L={L}, asset tree height={asset_tree_height}, account tree height={account_tree_height}"
    );

    println!(
        "Total proof size = {}",
        even_bp.compressed_size()
            + odd_bp.compressed_size()
            + leg_enc.compressed_size()
            + leg_creation_proof.compressed_size()
            + sender_proof.compressed_size()
            + receiver_proof.compressed_size()
    );
    println!(
        "Combined (settlement + receiver): proving time = {:?}",
        proving_time
    );
    println!("Sender: proving time = {:?}", sender_proving_time);
    println!(
        "verification time = {:?}, rmc verification time = {:?}",
        verification_time, rmc_verification_time
    );
}

#[cfg(NEVER)]
fn multi_asset_settlement() {
    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 4;
    const NUM_GENS: usize = 1 << 17;
    const L: usize = 512;

    let num_legs = 10;
    let asset_tree_height = 3;
    let account_tree_height = 4;

    let (
        asset_data_vec,
        asset_paths,
        asset_tree_root,
        legs,
        leg_encs,
        leg_enc_rands,
        alice_accounts,
        bob_accounts,
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_multi_asset_settlement::<NUM_GENS, L, ASSET_TREE_M, ACCOUNT_TREE_M>(
        num_legs,
        asset_tree_height,
        account_tree_height,
    );

    let mut rng = rand::thread_rng();
    let amount = 100;

    let nonce = b"multi_asset_settlement_nonce_txn_id_1";

    println!(
        "For settlement with {num_legs} legs, L={L}, ASSET_TREE_M={ASSET_TREE_M}, ACCOUNT_TREE_M={ACCOUNT_TREE_M}, asset tree height = {asset_tree_height}, account tree height = {account_tree_height}"
    );

    let start = Instant::now();
    let settlement_proof = SettlementCreationProof::new(
        &mut rng,
        legs,
        leg_encs.clone(),
        leg_enc_rands.clone(),
        asset_paths,
        asset_data_vec,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let settlement_proving_time = start.elapsed();
    let settlement_proof_size = settlement_proof.compressed_size() + leg_encs.compressed_size();

    println!(
        "Settlement: {settlement_proof_size} bytes and time = {:?}",
        settlement_proving_time
    );

    // Alice sends in all num_legs legs
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

    let start = Instant::now();
    let (alice_proof, alice_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new(
        &mut rng,
        alice_builders,
        alice_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let alice_proving_time = start.elapsed();
    let alice_proof_size = alice_proof.compressed_size();

    println!(
        "Sender: {alice_proof_size} bytes and time = {:?}",
        alice_proving_time
    );

    // Bob receives in all num_legs legs
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

    let start = Instant::now();
    let (bob_proof, bob_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new(
        &mut rng,
        bob_builders,
        bob_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let bob_proving_time = start.elapsed();
    let bob_proof_size = bob_proof.compressed_size();

    println!(
        "Receiver: {bob_proof_size} bytes and time = {:?}",
        bob_proving_time
    );

    let start = Instant::now();

    // Setup verifiers for Alice
    let mut alice_verifiers = Vec::new();
    for i in 0..num_legs {
        let verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(alice_updated_comms[i], alice_nullifiers[i], nonce);
        alice_verifiers.push(verifier);
    }

    for i in 0..num_legs {
        alice_verifiers[i].add_irreversible_send(leg_encs[i].clone());
    }

    // Setup verifiers for Bob
    let mut bob_verifiers = Vec::new();
    for i in 0..num_legs {
        let verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(bob_updated_comms[i], bob_nullifiers[i], nonce);
        bob_verifiers.push(verifier);
    }

    for i in 0..num_legs {
        bob_verifiers[i].add_irreversible_receive(leg_encs[i].clone());
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
            &mut rng,
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
            &mut rng,
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
            &mut rng,
            None,
        )
        .unwrap();

    // Asset tree uses opposite curves than account tree so merging accordingly
    let even_tuples = vec![settlement_odd, alice_even, bob_even];
    let odd_tuples = vec![settlement_even, alice_odd, bob_odd];

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let verify_time = start.elapsed();

    let start = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    // Verify proofs with RMC
    let (settlement_even, settlement_odd) = settlement_proof
        .verify_and_return_tuples(
            leg_encs.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_0),
        )
        .unwrap();

    let mut alice_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(alice_updated_comms[i], alice_nullifiers[i], nonce);
        verifier.add_irreversible_send(leg_encs[i].clone());
        alice_verifiers.push(verifier);
    }

    let (alice_even, alice_odd) = alice_proof
        .verify_and_return_tuples(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_0),
        )
        .unwrap();

    let mut bob_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(bob_updated_comms[i], bob_nullifiers[i], nonce);
        verifier.add_irreversible_receive(leg_encs[i].clone());
        bob_verifiers.push(verifier);
    }

    let (bob_even, bob_odd) = bob_proof
        .verify_and_return_tuples(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
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

    let verify_rmc_time = start.elapsed();

    println!(
        "For L={L}, asset tree height={asset_tree_height}, account tree height={account_tree_height}"
    );
    println!(
        "total proof size = {} bytes, regular verify time = {:?} and with rmc time = {:?}",
        settlement_proof_size + alice_proof_size + bob_proof_size,
        verify_time,
        verify_rmc_time
    );
}

#[cfg(NEVER)]
fn multi_asset_combined_create_and_send() {
    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 4;
    const NUM_GENS: usize = 1 << 17;
    const L: usize = 512;

    let num_legs = 10;
    let asset_tree_height = 3;
    let account_tree_height = 4;

    let (
        asset_data_vec,
        asset_paths,
        asset_tree_root,
        legs,
        leg_encs,
        leg_enc_rands,
        alice_accounts,
        bob_accounts,
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_multi_asset_settlement::<NUM_GENS, L, ASSET_TREE_M, ACCOUNT_TREE_M>(
        num_legs,
        asset_tree_height,
        account_tree_height,
    );

    let mut rng = rand::thread_rng();
    let amount = 100;

    let nonce = b"multi_asset_combined_nonce_txn_id_1";

    println!(
        "For combined settlement with {num_legs} legs, L={L}, ASSET_TREE_M={ASSET_TREE_M}, ACCOUNT_TREE_M={ACCOUNT_TREE_M}, asset tree height = {asset_tree_height}, account tree height = {account_tree_height}"
    );

    let start = Instant::now();

    let (mut even_prover, mut odd_prover) = tests_new_ct::create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof = SettlementCreationProof::new_with_given_prover(
        &mut rng,
        legs,
        leg_encs.clone(),
        leg_enc_rands.clone(),
        asset_paths,
        asset_data_vec,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover,
        &mut odd_prover,
    )
    .unwrap();

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

    let (alice_proof, alice_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover(
        &mut rng,
        alice_builders,
        alice_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut odd_prover,
        &mut even_prover,
    )
    .unwrap();

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let combined_proving_time = start.elapsed();

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

    let start = Instant::now();
    let (bob_proof, bob_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new(
        &mut rng,
        bob_builders,
        bob_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let bob_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    let mut alice_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(alice_updated_comms[i], alice_nullifiers[i], nonce);
        verifier.add_irreversible_send(leg_encs[i].clone());
        alice_verifiers.push(verifier);
    }

    alice_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            None,
        )
        .unwrap();

    let mut bob_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(bob_updated_comms[i], bob_nullifiers[i], nonce);
        verifier.add_irreversible_receive(leg_encs[i].clone());
        bob_verifiers.push(verifier);
    }

    let (bob_even, bob_odd) = bob_proof
        .verify_and_return_tuples(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let (even_tuple, odd_tuple) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let even_tuples = vec![odd_tuple, bob_even];
    let odd_tuples = vec![even_tuple, bob_odd];

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let verification_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let mut alice_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(alice_updated_comms[i], alice_nullifiers[i], nonce);
        verifier.add_irreversible_send(leg_encs[i].clone());
        alice_verifiers.push(verifier);
    }

    alice_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let mut bob_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(bob_updated_comms[i], bob_nullifiers[i], nonce);
        verifier.add_irreversible_receive(leg_encs[i].clone());
        bob_verifiers.push(verifier);
    }

    let (bob_even, bob_odd) = bob_proof
        .verify_and_return_tuples(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let even_tuples = vec![even_tuple_rmc, bob_odd];
    let odd_tuples = vec![odd_tuple_rmc, bob_even];

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

    let rmc_verification_time = start.elapsed();

    let combined_proof_size = leg_encs.compressed_size()
        + settlement_proof.compressed_size()
        + alice_proof.compressed_size()
        + even_bp.compressed_size()
        + odd_bp.compressed_size();

    let bob_proof_size = bob_proof.compressed_size();

    println!(
        "For L={L}, asset tree height={asset_tree_height}, account tree height={account_tree_height}"
    );
    println!(
        "Combined (settlement + alice): proving time = {:?}, proof size = {} bytes",
        combined_proving_time, combined_proof_size
    );
    println!(
        "Bob: proving time = {:?}, proof size = {} bytes",
        bob_proving_time, bob_proof_size
    );
    println!(
        "Total proof size = {} bytes, verification time = {:?}, rmc verification time = {:?}",
        combined_proof_size + bob_proof_size,
        verification_time,
        rmc_verification_time
    );
}

#[cfg(NEVER)]
fn multi_asset_combined_create_and_recv() {
    const NUM_GENS: usize = 1 << 17;
    const L: usize = 512;
    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 4;

    let num_legs = 10;
    let asset_tree_height = 3;
    let account_tree_height = 4;

    let (
        asset_data_vec,
        asset_paths,
        asset_tree_root,
        legs,
        leg_encs,
        leg_enc_rands,
        alice_accounts,
        bob_accounts,
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_key_gen,
        enc_gen,
    ) = setup_multi_asset_settlement::<NUM_GENS, L, ASSET_TREE_M, ACCOUNT_TREE_M>(
        num_legs,
        asset_tree_height,
        account_tree_height,
    );

    let mut rng = rand::thread_rng();
    let amount = 100;

    let nonce = b"multi_asset_combined_recv_nonce_txn_id_1";

    let start = Instant::now();

    let (mut even_prover, mut odd_prover) = tests_new_ct::create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof = SettlementCreationProof::new_with_given_prover(
        &mut rng,
        legs,
        leg_encs.clone(),
        leg_enc_rands.clone(),
        asset_paths,
        asset_data_vec,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
        &mut even_prover,
        &mut odd_prover,
    )
    .unwrap();

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

    let (bob_proof, bob_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover(
        &mut rng,
        bob_builders,
        bob_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
        &mut odd_prover,
        &mut even_prover,
    )
    .unwrap();

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let combined_proving_time = start.elapsed();

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

    let start = Instant::now();
    let (alice_proof, alice_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new(
        &mut rng,
        alice_builders,
        alice_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let alice_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    let mut bob_verifiers = Vec::new();
    for i in 0..num_legs {
        let verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(bob_updated_comms[i], bob_nullifiers[i], nonce);
        bob_verifiers.push(verifier);
    }

    for i in 0..num_legs {
        bob_verifiers[i].add_irreversible_receive(leg_encs[i].clone());
    }

    bob_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            None,
        )
        .unwrap();

    let (even_tuple, odd_tuple) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let mut alice_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(alice_updated_comms[i], alice_nullifiers[i], nonce);
        verifier.add_irreversible_send(leg_encs[i].clone());
        alice_verifiers.push(verifier);
    }

    let (alice_even, alice_odd) = alice_proof
        .verify_and_return_tuples(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let even_tuples = vec![odd_tuple, alice_even];
    let odd_tuples = vec![even_tuple, alice_odd];

    batch_verify_bp(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();

    let verification_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = tests_new_ct::create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let mut bob_verifiers = Vec::new();
    for i in 0..num_legs {
        let verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(bob_updated_comms[i], bob_nullifiers[i], nonce);
        bob_verifiers.push(verifier);
    }

    for i in 0..num_legs {
        bob_verifiers[i].add_irreversible_receive(leg_encs[i].clone());
    }

    bob_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (even_tuple_rmc, odd_tuple_rmc) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let mut alice_verifiers = Vec::new();
    for i in 0..num_legs {
        let mut verifier = AccountStateTransitionProofVerifier::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::init(alice_updated_comms[i], alice_nullifiers[i], nonce);
        verifier.add_irreversible_send(leg_encs[i].clone());
        alice_verifiers.push(verifier);
    }

    let (alice_even, alice_odd) = alice_proof
        .verify_and_return_tuples(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
        )
        .unwrap();

    let even_tuples = vec![odd_tuple_rmc, alice_even];
    let odd_tuples = vec![even_tuple_rmc, alice_odd];

    add_verification_tuples_batches_to_rmc(
        even_tuples,
        odd_tuples,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rmc_1,
        &mut rmc_0,
    )
    .unwrap();

    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let rmc_verification_time = start.elapsed();

    let combined_proof_size = leg_encs.compressed_size()
        + settlement_proof.compressed_size()
        + bob_proof.compressed_size()
        + even_bp.compressed_size()
        + odd_bp.compressed_size();

    let alice_proof_size = alice_proof.compressed_size();

    println!(
        "For L={L}, asset tree height={asset_tree_height}, account tree height={account_tree_height}"
    );
    println!(
        "Combined (settlement + receiver): proving time = {:?}, proof size = {} bytes",
        combined_proving_time, combined_proof_size
    );
    println!(
        "Sender: proving time = {:?}, proof size = {} bytes",
        alice_proving_time, alice_proof_size
    );
    println!(
        "Total proof size = {} bytes, verification time = {:?}, rmc verification time = {:?}",
        combined_proof_size + alice_proof_size,
        verification_time,
        rmc_verification_time
    );
}

#[cfg(NEVER)]
fn multi_asset_state_transition_different_confs() {
    fn check<const L: usize, const M: usize>(
        num_legs: usize,
        height: usize,
        account_tree_params: &SelRerandProofParameters<PallasParameters, VestaParameters>,
        account_comm_key: impl AccountCommitmentKeyTrait<PallasA> + Clone,
        enc_key_gen: PallasA,
        enc_gen: PallasA,
    ) {
        let mut rng = rand::thread_rng();

        let (
            ((sk_alice, pk_alice), (_, pk_alice_e)),
            ((sk_bob, pk_bob), (_, pk_bob_e)),
            (_, (_, pk_auditor_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        // Create legs, all with same sender (Alice) and receiver (Bob) but different assets
        let mut leg_encs = Vec::with_capacity(num_legs);
        let mut leg_enc_rands = Vec::with_capacity(num_legs);
        let amount = 100;

        for asset_id in 1..=num_legs as u32 {
            let (_, leg_enc, leg_enc_rand) = tests_new_ct::setup_leg(
                &mut rng,
                pk_bob.0,
                pk_alice.0,
                pk_auditor_e.0,
                true,
                amount,
                asset_id,
                pk_bob_e.0,
                pk_alice_e.0,
                enc_key_gen,
                enc_gen,
            );
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
        }

        // Create Alice's accounts, one per asset
        let alice_id = PallasFr::rand(&mut rng);
        let mut alice_accounts = Vec::with_capacity(num_legs);
        let mut alice_account_comms = Vec::with_capacity(num_legs);

        for asset_id in 1..=num_legs as u32 {
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_alice.clone(), alice_id);
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
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_bob.clone(), bob_id);
            account.balance = 300;
            let comm = account.commit(account_comm_key.clone()).unwrap();
            bob_account_comms.push(comm.0);
            bob_accounts.push(account);
        }

        // Create account tree with all accounts
        let mut all_account_comms = Vec::with_capacity(2 * num_legs);
        all_account_comms.extend_from_slice(&alice_account_comms);
        all_account_comms.extend_from_slice(&bob_account_comms);

        let account_tree = CurveTree::<L, M, PallasParameters, VestaParameters>::from_leaves(
            &all_account_comms,
            account_tree_params,
            Some(height),
        );
        let account_tree_root = account_tree.root_node();

        let nonce = b"multi_asset_settlement_nonce_txn_id_1";

        println!("\nFor {num_legs} legs, L={L}, M={M}, height={height}");

        // Alice receives in all num_legs legs
        let mut alice_builders = Vec::with_capacity(num_legs);
        let mut alice_updated_comms = Vec::with_capacity(num_legs);

        for i in 0..num_legs {
            let updated_account = alice_accounts[i].get_state_for_receive();
            let updated_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            alice_updated_comms.push(updated_comm);

            let mut builder = AccountStateTransitionProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::init(
                alice_accounts[i].clone(),
                updated_account,
                updated_comm,
                nonce,
            );
            builder.add_receive_affirmation(leg_encs[i].clone(), leg_enc_rands[i].clone());
            alice_builders.push(builder);
        }

        // Get paths for Alice's accounts in batches
        let mut alice_paths = Vec::new();
        for chunk in (0..num_legs).collect::<Vec<_>>().chunks(M) {
            let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
            let path = account_tree.get_paths_to_leaves(&indices).unwrap();
            alice_paths.push(path);
        }

        let start = Instant::now();
        let (alice_proof, alice_nullifiers) =
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new(
                &mut rng,
                alice_builders,
                alice_paths,
                &account_tree_root,
                account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let alice_proving_time = start.elapsed();
        let alice_proof_size = alice_proof.compressed_size();

        println!(
            "Alice (receive affirmation): {alice_proof_size} bytes and time = {:?}",
            alice_proving_time
        );

        let start = Instant::now();

        // Setup verifiers for Alice
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
            verifier.add_receive_affirmation(leg_encs[i].clone());
            alice_verifiers.push(verifier);
        }

        let (alice_even, alice_odd) = alice_proof
            .verify_and_return_tuples(
                alice_verifiers,
                &account_tree_root,
                account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let even_tuples = vec![alice_even];
        let odd_tuples = vec![alice_odd];

        batch_verify_bp(
            even_tuples,
            odd_tuples,
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
        )
        .unwrap();

        let verify_time = start.elapsed();

        let start = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

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
            verifier.add_receive_affirmation(leg_encs[i].clone());
            alice_verifiers.push(verifier);
        }

        let (alice_even, alice_odd) = alice_proof
            .verify_and_return_tuples(
                alice_verifiers,
                &account_tree_root,
                account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                Some(&mut rmc_0),
            )
            .unwrap();

        let even_tuples = vec![alice_even];
        let odd_tuples = vec![alice_odd];

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

        let verify_rmc_time = start.elapsed();

        println!(
            "Regular verify time = {:?} and with rmc time = {:?}",
            verify_time, verify_rmc_time
        );
    }

    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<{ 1 << 19 }>(b"test");

    check::<512, 2>(
        8,
        4,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
    check::<512, 4>(
        8,
        4,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
    check::<1024, 2>(
        8,
        3,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
    check::<1024, 4>(
        8,
        3,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
    check::<2000, 2>(
        8,
        3,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
    check::<2000, 4>(
        8,
        3,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
    check::<2048, 2>(
        8,
        3,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
    check::<2048, 4>(
        8,
        3,
        &account_tree_params,
        account_comm_key.clone(),
        enc_key_gen,
        enc_gen,
    );
}

// Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

#[cfg(feature = "ignore_prover_input_sanitation")]
mod input_sanitation_disabled {
    use crate::account::tests_old::*;
    use state::AccountCommitmentKeyTrait;
    use crate::account::tests_new_ct::{get_tree_with_account_comm, setup_leg};

    #[test]
    fn keep_balance_same_in_send_txn() {
        // A sender account sends AffirmAsSenderTxnProof but does not decrease the balance from his account. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (_, pk_s_e)),
            ((_, pk_r), (_, pk_r_e)),
            ((_, _), (_, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            4,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Create an updated account that doesn't decrease the balance
        let mut updated_account = account.get_state_for_send(amount).unwrap();
        updated_account.balance = account.balance; // Keep same balance

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = AffirmAsSenderTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        // Create an updated account that instead increases the balance
        let mut updated_account = account.get_state_for_send(amount).unwrap();
        updated_account.balance = account.balance + amount; // Increase balance

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = AffirmAsSenderTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc,
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn increase_balance_in_receive_txn() {
        // A receiver account sends AffirmAsReceiverTxnProof but increases the balance. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((_, pk_s), (_, pk_s_e)),
            ((sk_r, pk_r), (_, pk_r_e)),
            ((_, _), (_, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            4,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Create a malicious updated account that increases balance
        let mut updated_account = account.get_state_for_receive();
        updated_account.balance = account.balance + amount;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = AffirmAsReceiverTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn increase_balance_incorrectly_during_claiming_received_funds() {
        // A receiver account sends ClaimReceivedTxnProof but increases the balance more than the actual claim amount. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((_, pk_s), (_, pk_s_e)),
            ((sk_r, pk_r), (_, pk_r_e)),
            ((_, _), (_, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
        // Assume that account had some balance and it had sent the receive transaction to increase its counter
        account.balance = 200;
        account.counter += 2;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            4,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Update account that increases balance more than the actual claim amount
        let mut updated_account = account.get_state_for_claiming_received(amount).unwrap();
        updated_account.balance = account.balance + 75; // Add extra on top of the actual amount

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = ClaimReceivedTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        // Update account with counter decreased by 1 more than it should be
        let mut updated_account = account.get_state_for_claiming_received(amount).unwrap();
        updated_account.counter -= 1;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = ClaimReceivedTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc,
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn increase_balance_in_counter_update_by_sender() {
        // A sender account sends SenderCounterUpdateTxnProof but increases their balance when it should remain the same. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (_, pk_s_e)),
            ((_, pk_r), (_, pk_r_e)),
            ((_, _), (_, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account with non-zero counter
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
        account.balance = 50;
        account.counter = 2;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            4,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Update account that increases balance when it should remain the same
        let mut updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        updated_account.balance = account.balance + amount;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderCounterUpdateTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        // Update account with counter decreased by 1 more than it should be
        let mut updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        updated_account.counter -= 1;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderCounterUpdateTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc,
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn incorrect_updates_in_reverse_send_txn() {
        // A sender account sends SenderReverseTxnProof but makes incorrect updates to balance or counter. These proofs should fail
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
        // Assume that account had some balance and it had sent the send transaction to increase its counter
        account.balance = 200;
        account.counter += 2;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            4,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Update account that increases balance more than required
        let mut updated_account = account.get_state_for_reversing_send(amount).unwrap();
        updated_account.balance = account.balance + 50; // Add extra on top of the actual amount

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderReverseTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        // Update account with counter decreased by 1 more than it should be
        let mut updated_account = account.get_state_for_reversing_send(amount).unwrap();
        updated_account.counter -= 1;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderReverseTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc,
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn incorrect_updates_in_single_shot_settlement() {
        // Test malicious updates in single shot settlement (irreversible send/receive)
        // These proofs should fail because balance or counter updates are incorrect
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"testing");

        let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            true,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Create sender account
        let sender_id = PallasFr::rand(&mut rng);
        let (mut sender_account, _, _) = new_account(&mut rng, asset_id, sk_s.clone(), sender_id);
        sender_account.balance = 200; // Ensure sufficient balance
        sender_account.counter = 5; // Set non-zero counter for testing
        let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

        // Create receiver account
        let receiver_id = PallasFr::rand(&mut rng);
        let (mut receiver_account, _, _) = new_account(&mut rng, asset_id, sk_r, receiver_id);
        receiver_account.balance = 150; // Some initial balance
        receiver_account.counter = 3; // Set non-zero counter for testing
        let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();

        // Create the account tree with both accounts
        let account_comms = vec![sender_account_comm.0, receiver_account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(2),
        );

        let account_tree_root = account_tree.root_node();
        let sender_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let receiver_path = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

        let nonce = b"test-nonce";

        // Sender trying to decrease balance less than amount
        // Should decrease by 100, but only decreases by 50
        let mut malicious_sender_account = sender_account
            .get_state_for_irreversible_send(amount)
            .unwrap();
        malicious_sender_account.balance += 50;

        let malicious_sender_comm = malicious_sender_account
            .commit(account_comm_key.clone())
            .unwrap();

        let (proof, nullifier) = IrreversibleAffirmAsSenderTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &sender_account,
            &malicious_sender_account,
            malicious_sender_comm,
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &account_tree_root,
                    malicious_sender_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        // Receiver trying to increase balance more than amount
        // Should increase by 100, but increases by 150
        let mut malicious_receiver_account = receiver_account
            .get_state_for_irreversible_receive(amount)
            .unwrap();
        malicious_receiver_account.balance += 50;

        let malicious_receiver_comm = malicious_receiver_account
            .commit(account_comm_key.clone())
            .unwrap();

        let (proof, nullifier) = IrreversibleAffirmAsReceiverTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &receiver_account,
            &malicious_receiver_account,
            malicious_receiver_comm,
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &account_tree_root,
                    malicious_receiver_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        // Sender trying to decrease counter
        let mut malicious_sender_account = sender_account
            .get_state_for_irreversible_send(amount)
            .unwrap();
        malicious_sender_account.counter -= 1;

        let malicious_sender_comm = malicious_sender_account
            .commit(account_comm_key.clone())
            .unwrap();

        let (proof, nullifier) = IrreversibleAffirmAsSenderTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &sender_account,
            &malicious_sender_account,
            malicious_sender_comm,
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    &account_tree_root,
                    malicious_sender_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        // Receiver trying to decrease counter
        let mut malicious_receiver_account = receiver_account
            .get_state_for_irreversible_receive(amount)
            .unwrap();
        malicious_receiver_account.counter -= 1;

        let malicious_receiver_comm = malicious_receiver_account
            .commit(account_comm_key.clone())
            .unwrap();

        let (proof, nullifier) = IrreversibleAffirmAsReceiverTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &receiver_account,
            &malicious_receiver_account,
            malicious_receiver_comm,
            receiver_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc,
                    &account_tree_root,
                    malicious_receiver_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );
    }

    // More tests can be added like secret key mismatch, incorrect rho or randomness creation, etc.
}
