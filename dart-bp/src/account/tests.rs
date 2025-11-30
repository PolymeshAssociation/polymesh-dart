use crate::account::*;
use crate::account_registration::tests::{new_account, setup_comm_key};
use crate::leg::tests::setup_keys;
use crate::leg::{
    AssetCommitmentParams, AssetData, LEG_TXN_EVEN_LABEL, LEG_TXN_ODD_LABEL, Leg, LegCreationProof,
    LegEncryption, LegEncryptionRandomness, MEDIATOR_TXN_LABEL, MediatorTxnProof, SettlementCreationProof,
};
use crate::util::{
    add_verification_tuples_batches_to_rmc, batch_verify_bp, get_verification_tuples_with_rng,
    verify_rmc, verify_with_rng,
};
use ark_ec::CurveGroup;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use blake2::Blake2b512;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use curve_tree_relations::curve_tree::CurveTree;
use polymesh_dart_common::{AssetId, Balance};
use rand_core::CryptoRngCore;
use std::time::Instant;

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;
type PallasA = ark_pallas::Affine;
type PallasFr = ark_pallas::Fr;
type VestaFr = ark_vesta::Fr;

fn setup_leg<R: CryptoRngCore>(
    rng: &mut R,
    pk_s: PallasA,
    pk_r: PallasA,
    pk_a_e: PallasA,
    amount: Balance,
    asset_id: AssetId,
    pk_s_e: PallasA,
    pk_r_e: PallasA,
    enc_key_gen: PallasA,
    enc_gen: PallasA,
) -> (
    Leg<PallasA>,
    LegEncryption<PallasA>,
    LegEncryptionRandomness<PallasFr>,
) {
    let leg = Leg::new(pk_s, pk_r, vec![(true, pk_a_e)], amount, asset_id).unwrap();
    let (leg_enc, leg_enc_rand) = leg
        .encrypt::<_, Blake2b512>(rng, pk_s_e, pk_r_e, enc_key_gen, enc_gen)
        .unwrap();
    (leg, leg_enc, leg_enc_rand)
}

/// Create a new tree and add the given account's commitment to the tree and return the tree
/// In future, allow to generate tree many given number of leaves and add the account commitment to a
/// random position in tree.
pub fn get_tree_with_account_comm<const L: usize>(
    account: &AccountState<PallasA>,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    account_tree_params: &SelRerandParameters<PallasParameters, VestaParameters>,
) -> Result<CurveTree<L, 1, PallasParameters, VestaParameters>> {
    let account_comm = account.commit(account_comm_key)?;

    // Add account commitment in curve tree
    let set = vec![account_comm.0];
    Ok(
        CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            account_tree_params,
            Some(4),
        ),
    )
}

pub fn setup_gens<const NUM_GENS: usize>(
    label: &[u8],
) -> (
    SelRerandParameters<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
    PallasA,
) {
    // Create public params (generators, etc)
    let account_tree_params =
        SelRerandParameters::<PallasParameters, VestaParameters>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();
    let account_comm_key = setup_comm_key(label);
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();
    (account_tree_params, account_comm_key, enc_key_gen, enc_gen)
}

#[test]
fn send_txn() {
    let mut rng = rand::thread_rng();

    // Setup begins
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

    let account_tree =
        get_tree_with_account_comm::<L>(&account, account_comm_key.clone(), &account_tree_params)
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

    println!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[test]
fn receive_txn() {
    let mut rng = rand::thread_rng();

    // Setup beings

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (
        ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
        ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
        ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
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
    let account_tree =
        get_tree_with_account_comm::<L>(&account, account_comm_key.clone(), &account_tree_params)
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

    log::info!("total proof size = {}", proof.compressed_size());
    println!(
        "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        prover_time, verifier_time, verifier_time_rmc
    );
}

#[test]
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
        ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
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

    let account_tree =
        get_tree_with_account_comm::<L>(&account, account_comm_key.clone(), &account_tree_params)
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

#[test]
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
        ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
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

    let account_tree =
        get_tree_with_account_comm::<L>(&account, account_comm_key.clone(), &account_tree_params)
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

#[test]
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
        ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_, leg_enc, leg_enc_rand) = setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
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

    let account_tree =
        get_tree_with_account_comm::<L>(&account, account_comm_key.clone(), &account_tree_params)
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

#[test]
fn reverse_receive_txn() {
    // This is similar to receive txn as only account's counter is decreased, balance remains same.

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (
        ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
        ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
        ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
    ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    let (_leg, leg_enc, leg_enc_rand) = setup_leg(
        &mut rng,
        pk_s.0,
        pk_r.0,
        pk_a_e.0,
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

    let account_tree =
        get_tree_with_account_comm::<L>(&account, account_comm_key.clone(), &account_tree_params)
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

#[test]
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
        let ((sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
        let ((_sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
        let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
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

    batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

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
        &account_tree_params,
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

#[test]
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
        let ((sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
        let ((_sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
        let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
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
    let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript,
    );
    let mut odd_prover = Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

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

    let (even_bp, odd_bp) =
        prove_with_rng(even_prover, odd_prover, &account_tree_params, &mut rng).unwrap();
    let proving_time = clock.elapsed();

    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_verifier = Verifier::new(transcript_even);
    let mut odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let verification_time = clock.elapsed();

    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_verifier = Verifier::new(transcript_even);
    let mut odd_verifier = Verifier::new(transcript_odd);
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
        &account_tree_params,
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

#[test]
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
        let ((_sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
        let ((sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
        let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
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

    batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

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
        &account_tree_params,
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

#[test]
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
        let ((_sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
        let ((sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
        let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
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
    let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript,
    );
    let mut odd_prover = Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

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

    let (even_bp, odd_bp) =
        prove_with_rng(even_prover, odd_prover, &account_tree_params, &mut rng).unwrap();
    let proving_time = clock.elapsed();

    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_verifier = Verifier::new(transcript_even);
    let mut odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let verification_time = clock.elapsed();

    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_verifier = Verifier::new(transcript_even);
    let mut odd_verifier = Verifier::new(transcript_odd);
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
        &account_tree_params,
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

#[test]
fn single_shot_settlement() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_tree_params = SelRerandParameters {
        even_parameters: account_tree_params.odd_parameters.clone(),
        odd_parameters: account_tree_params.even_parameters.clone(),
    };

    let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let asset_id = 1;
    let amount = 100;

    // Create asset commitment parameters
    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params-for-single-settlement",
        2, // 1 auditor + 1 mediator
        &asset_tree_params.even_parameters.bp_gens,
    );

    // Create AssetData - use auditor key as the sole key
    let keys = vec![(true, pk_a_e.0)]; // Single auditor key
    let asset_data = AssetData::new(
        asset_id,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.delta,
    )
    .unwrap();

    // Create asset tree with the asset commitment
    let set = vec![asset_data.commitment];
    let asset_tree =
        CurveTree::<L, 1, ark_vesta::VestaConfig, ark_pallas::PallasConfig>::from_leaves(
            &set,
            &asset_tree_params,
            Some(3),
        );

    // Get asset tree path
    let asset_path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    // Create a single leg
    let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
    let (leg_enc, leg_enc_rand) = leg
        .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
        .unwrap();

    // Create sender account
    let sender_id = PallasFr::rand(&mut rng);
    let (mut sender_account, _, _) = new_account(&mut rng, asset_id, sk_s, sender_id);
    sender_account.balance = 200; // Ensure sufficient balance
    let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

    // Create receiver account
    let receiver_id = PallasFr::rand(&mut rng);
    let (mut receiver_account, _, _) = new_account(&mut rng, asset_id, sk_r, receiver_id);
    receiver_account.balance = 150; // Some initial balance
    let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();

    // Create the account tree with both accounts
    let account_comms = vec![sender_account_comm.0, receiver_account_comm.0];
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &account_comms,
        &account_tree_params,
        Some(4),
    );

    let account_tree_root = account_tree.root_node();

    // Prepare updated account states
    let updated_sender_account = sender_account
        .get_state_for_irreversible_send(amount)
        .unwrap();
    assert_eq!(
        updated_sender_account.balance,
        sender_account.balance - amount
    );
    assert_eq!(updated_sender_account.counter, sender_account.counter);
    let updated_sender_account_comm = updated_sender_account
        .commit(account_comm_key.clone())
        .unwrap();
    let sender_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_receiver_account = receiver_account
        .get_state_for_irreversible_receive(amount)
        .unwrap();
    assert_eq!(
        updated_receiver_account.balance,
        receiver_account.balance + amount
    );
    assert_eq!(updated_receiver_account.counter, receiver_account.counter);
    let updated_receiver_account_comm = updated_receiver_account
        .commit(account_comm_key.clone())
        .unwrap();
    let receiver_path = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    let nonce = b"single_shot_settlement_nonce_txn_id_1";

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

    // Asset tree uses opposite curves than account tree so merging accordingly
    let even_tuples = vec![settlement_odd, sender_even, receiver_even];
    let odd_tuples = vec![settlement_even, sender_odd, receiver_odd];

    batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

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
        &account_tree_params,
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();
    let verifier_rmc_time = start.elapsed();

    println!(
        "proof size = {}, verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
        settlement_proof.compressed_size() + leg_enc.compressed_size() + receiver_proof.compressed_size() + sender_proof.compressed_size(), verifier_time, verifier_rmc_time
    );
}

#[test]
fn swap_settlement() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 2;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_tree_params = SelRerandParameters {
        even_parameters: account_tree_params.odd_parameters.clone(),
        odd_parameters: account_tree_params.even_parameters.clone(),
    };

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        &asset_tree_params.even_parameters.bp_gens,
    );

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (sk_m_e, pk_m_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Both assets have same mediator
    let keys = vec![(false, pk_m_e.0)];
    let asset_data_1 = AssetData::new(
        asset_id_1,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.delta,
    )
    .unwrap();
    let asset_data_2 = AssetData::new(
        asset_id_2,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.delta,
    )
    .unwrap();

    let set = vec![asset_data_1.commitment, asset_data_2.commitment];
    let asset_tree =
        CurveTree::<L, 1, ark_vesta::VestaConfig, ark_pallas::PallasConfig>::from_leaves(
            &set,
            &asset_tree_params,
            Some(3),
        );
    let asset_path_1 = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_path_2 = asset_tree.get_path_to_leaf_for_proof(1, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    // Create two legs for swap
    let leg_1 = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount_1, asset_id_1).unwrap();
    let (leg_enc_1, leg_enc_rand_1) = leg_1
        .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
        .unwrap();
    let leg_2 = Leg::new(pk_r.0, pk_s.0, keys.clone(), amount_2, asset_id_2).unwrap();
    let (leg_enc_2, leg_enc_rand_2) = leg_2
        .encrypt::<_, Blake2b512>(&mut rng, pk_r_e.0, pk_s_e.0, enc_key_gen, enc_gen)
        .unwrap();

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
        Some(4),
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
    let even_transcript_settlement = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let odd_transcript_settlement = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut even_prover_settlement = Prover::new(
        &asset_tree_params.even_parameters.pc_gens,
        even_transcript_settlement,
    );
    let mut odd_prover_settlement = Prover::new(
        &asset_tree_params.odd_parameters.pc_gens,
        odd_transcript_settlement,
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
        &asset_tree_params,
        &mut rng,
    )
    .unwrap();
    let settlement_proving_time = clock.elapsed();

    // Verify settlement proofs (both legs)
    let clock = Instant::now();

    let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut settlement_even_verifier = Verifier::new(transcript_even);
    let mut settlement_odd_verifier = Verifier::new(transcript_odd);

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
        &asset_tree_params,
        &mut rng,
    )
    .unwrap();
    let settlement_verification_time = clock.elapsed();

    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    // Verify settlement proofs (both legs)
    let clock = Instant::now();

    let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut settlement_even_verifier = Verifier::new(transcript_even);
    let mut settlement_odd_verifier = Verifier::new(transcript_odd);

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
        &asset_tree_params,
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
    let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_alice = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_alice,
    );
    let mut odd_prover_alice = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_alice,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let alice_proving_time = clock.elapsed();

    // Combined bob proofs for both legs (bob receives leg1, sends leg2)
    let clock = Instant::now();
    let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_bob = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_bob,
    );
    let mut odd_prover_bob = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_bob,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let bob_proving_time = clock.elapsed();

    // Verify alice proofs (both legs)
    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let alice_verification_time = clock.elapsed();

    // Verify bob proofs (both legs)
    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let bob_verification_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let alice_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
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
    let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_alice = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_alice,
    );
    let mut odd_prover_alice = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_alice,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();

    let alice_counter_update_proving_time = clock.elapsed();

    // Bob counter update proving
    let clock = Instant::now();

    // Bob counter updates with his own provers
    let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_bob = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_bob,
    );
    let mut odd_prover_bob = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_bob,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();

    let bob_counter_update_proving_time = clock.elapsed();

    // Verify counter update proofs
    // Alice counter update verification
    let clock = Instant::now();

    // Verify Alice counter update proofs
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();

    let alice_counter_update_verification_time = clock.elapsed();

    // Bob counter update verification
    let clock = Instant::now();

    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();

    let bob_counter_update_verification_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let alice_counter_update_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
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

#[test]
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

    let keys = vec![(true, pk_a_e.0)];
    // Create two legs for swap
    let leg_1 = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount_1, asset_id_1).unwrap();
    let (leg_enc_1, leg_enc_rand_1) = leg_1
        .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
        .unwrap();
    let leg_2 = Leg::new(pk_r.0, pk_s.0, keys.clone(), amount_2, asset_id_2).unwrap();
    let (leg_enc_2, leg_enc_rand_2) = leg_2
        .encrypt::<_, Blake2b512>(&mut rng, pk_r_e.0, pk_s_e.0, enc_key_gen, enc_gen)
        .unwrap();

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
    let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_alice = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_alice,
    );
    let mut odd_prover_alice = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_alice,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let alice_proving_time = clock.elapsed();

    // Combined bob proofs for both legs (bob reverses receive in leg1, reverses send in leg2)
    let clock = Instant::now();
    let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_bob = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_bob,
    );
    let mut odd_prover_bob = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_bob,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let bob_proving_time = clock.elapsed();

    // Verify alice proofs (both legs)
    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let alice_verification_time = clock.elapsed();

    // Verify bob proofs (both legs)
    let clock = Instant::now();
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();
    let bob_verification_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let alice_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
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

#[test]
fn single_shot_swap() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 2;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"testing");

    let asset_tree_params = SelRerandParameters {
        even_parameters: account_tree_params.odd_parameters.clone(),
        odd_parameters: account_tree_params.even_parameters.clone(),
    };

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        &asset_tree_params.even_parameters.bp_gens,
    );

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
        asset_tree_params.odd_parameters.delta,
    )
    .unwrap();
    let asset_data_2 = AssetData::new(
        asset_id_2,
        keys.clone(),
        &asset_comm_params,
        asset_tree_params.odd_parameters.delta,
    )
    .unwrap();

    let set = vec![asset_data_1.commitment, asset_data_2.commitment];
    let asset_tree =
        CurveTree::<L, 1, ark_vesta::VestaConfig, ark_pallas::PallasConfig>::from_leaves(
            &set,
            &asset_tree_params,
            Some(2),
        );
    let asset_path_1 = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_path_2 = asset_tree.get_path_to_leaf_for_proof(1, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    // Create two legs for swap
    let leg_1 = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount_1, asset_id_1).unwrap();
    let (leg_enc_1, leg_enc_rand_1) = leg_1
        .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
        .unwrap();
    let leg_2 = Leg::new(pk_r.0, pk_s.0, keys.clone(), amount_2, asset_id_2).unwrap();
    let (leg_enc_2, leg_enc_rand_2) = leg_2
        .encrypt::<_, Blake2b512>(&mut rng, pk_r_e.0, pk_s_e.0, enc_key_gen, enc_gen)
        .unwrap();

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
    let even_transcript_settlement = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let odd_transcript_settlement = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut even_prover_settlement = Prover::new(
        &asset_tree_params.even_parameters.pc_gens,
        even_transcript_settlement,
    );
    let mut odd_prover_settlement = Prover::new(
        &asset_tree_params.odd_parameters.pc_gens,
        odd_transcript_settlement,
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
        &asset_tree_params,
        &mut rng,
    )
    .unwrap();

    // Combined proofs for Alice (sending in leg1, receiving in leg2)
    let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_alice = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_alice,
    );
    let mut odd_prover_alice = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_alice,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();

    // Combined proofs for Bob (receiving in leg1, sending in leg2)
    let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
    let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut even_prover_bob = Prover::new(
        &account_tree_params.even_parameters.pc_gens,
        even_transcript_bob,
    );
    let mut odd_prover_bob = Prover::new(
        &account_tree_params.odd_parameters.pc_gens,
        odd_transcript_bob,
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
        &account_tree_params,
        &mut rng,
    )
    .unwrap();

    // Verify all proofs
    let clock = Instant::now();

    let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut settlement_even_verifier = Verifier::new(transcript_even);
    let mut settlement_odd_verifier = Verifier::new(transcript_odd);

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
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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

    batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

    let verifier_time = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut settlement_even_verifier = Verifier::new(transcript_even);
    let mut settlement_odd_verifier = Verifier::new(transcript_odd);

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
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut alice_even_verifier = Verifier::new(transcript_even);
    let mut alice_odd_verifier = Verifier::new(transcript_odd);

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
    let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
    let mut bob_even_verifier = Verifier::new(transcript_even);
    let mut bob_odd_verifier = Verifier::new(transcript_odd);

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
        &account_tree_params,
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

#[test]
fn multi_asset_settlement() {
    let mut rng = rand::thread_rng();

    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 4;

    const NUM_GENS: usize = 1 << 17;
    const L: usize = 512;
    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        setup_gens::<NUM_GENS>(b"test");

    // Asset tree uses opposite curves
    let asset_tree_params = SelRerandParameters {
        even_parameters: account_tree_params.odd_parameters.clone(),
        odd_parameters: account_tree_params.even_parameters.clone(),
    };

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        &asset_tree_params.even_parameters.bp_gens,
    );

    // Setup keys for Alice (sender), Bob (receiver), and auditor
    let (((sk_alice, pk_alice), (_, pk_alice_e)), ((sk_bob, pk_bob), (_, pk_bob_e)), (_, (_, pk_auditor_e))) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let num_legs = 32;
    let keys = vec![(true, pk_auditor_e.0)];
    let mut asset_data_vec = Vec::with_capacity(num_legs);
    let mut asset_commitments = Vec::with_capacity(num_legs);
    
    for asset_id in 1..=num_legs as u32 {
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();
        asset_commitments.push(asset_data.commitment);
        asset_data_vec.push(asset_data);
    }

    let asset_tree_height = 3;
    let account_tree_height = 4;

    let asset_tree =
        CurveTree::<L, ASSET_TREE_M, VestaParameters, PallasParameters>::from_leaves(
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

    // Get asset tree paths for all legs (all assets are in the tree)
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

    // Create account tree with all accounts, Alice's num_legs accounts, then Bob's num_legs accounts
    let mut all_account_comms = Vec::with_capacity(2 * num_legs);
    all_account_comms.extend_from_slice(&alice_account_comms);
    all_account_comms.extend_from_slice(&bob_account_comms);
    
    let account_tree = CurveTree::<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>::from_leaves(
        &all_account_comms,
        &account_tree_params,
        Some(account_tree_height),
    );
    let account_tree_root = account_tree.root_node();

    let nonce = b"multi_asset_settlement_nonce_txn_id_1";

    println!("For settlement with {num_legs} legs, L={L}, ASSET_TREE_M={ASSET_TREE_M}, ACCOUNT_TREE_M={ACCOUNT_TREE_M}, asset tree height = {asset_tree_height}, account tree height = {account_tree_height}");

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

    println!("Settlement: {settlement_proof_size} bytes and time = {:?}", settlement_proving_time);

    // Alice sends in all num_legs legs
    let mut alice_builders = Vec::with_capacity(num_legs);
    let mut alice_updated_comms = Vec::with_capacity(num_legs);
    
    for i in 0..num_legs {
        let updated_account = alice_accounts[i]
            .get_state_for_irreversible_send(amount)
            .unwrap();
        let updated_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        alice_updated_comms.push(updated_comm);
        
        let mut builder = AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
            alice_accounts[i].clone(),
            updated_account,
            updated_comm,
            nonce,
        );
        builder.add_irreversible_send(
            amount,
            leg_encs[i].clone(),
            leg_enc_rands[i].clone(),
        );
        alice_builders.push(builder);
    }

    // Get paths for Alice's accounts in batches
    let mut alice_paths = Vec::new();
    for chunk in (0..num_legs).collect::<Vec<_>>().chunks(ACCOUNT_TREE_M) {
        let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
        let path = account_tree.get_paths_to_leaves(&indices).unwrap();
        alice_paths.push(path);
    }

    let start = Instant::now();
    let (alice_proof, alice_nullifiers) =
        MultiAssetStateTransitionProof::<L, ACCOUNT_TREE_M, _, _, PallasParameters, VestaParameters>::new(
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

    println!("Sender: {alice_proof_size} bytes and time = {:?}", alice_proving_time);

    // Bob receives in all num_legs legs
    let mut bob_builders = Vec::with_capacity(num_legs);
    let mut bob_updated_comms = Vec::with_capacity(num_legs);
    
    for i in 0..num_legs {
        let updated_account = bob_accounts[i]
            .get_state_for_irreversible_receive(amount)
            .unwrap();
        let updated_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        bob_updated_comms.push(updated_comm);
        
        let mut builder = AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
            bob_accounts[i].clone(),
            updated_account,
            updated_comm,
            nonce,
        );
        builder.add_irreversible_receive(amount, leg_encs[i].clone(), leg_enc_rands[i].clone());
        bob_builders.push(builder);
    }

    // Get paths for Bob's accounts in batches
    let mut bob_paths = Vec::new();
    for chunk in (num_legs..2*num_legs).collect::<Vec<_>>().chunks(ACCOUNT_TREE_M) {
        let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
        let path = account_tree.get_paths_to_leaves(&indices).unwrap();
        bob_paths.push(path);
    }

    let start = Instant::now();
    let (bob_proof, bob_nullifiers) =
        MultiAssetStateTransitionProof::<L, ACCOUNT_TREE_M, _, _, PallasParameters, VestaParameters>::new(
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

    println!("Receiver: {bob_proof_size} bytes and time = {:?}", bob_proving_time);

    let start = Instant::now();

    // Setup verifiers for Alice
    let mut alice_verifiers = Vec::new();
    for i in 0..num_legs {
        let verifier = AccountStateTransitionProofVerifier::<L, _, _, PallasParameters, VestaParameters>::init(
            alice_updated_comms[i],
            alice_nullifiers[i],
            nonce,
        );
        alice_verifiers.push(verifier);
    }
    
    for i in 0..num_legs {
        alice_verifiers[i].add_irreversible_send(leg_encs[i].clone());
    }

    // Setup verifiers for Bob
    let mut bob_verifiers = Vec::new();
    for i in 0..num_legs {
        let verifier = AccountStateTransitionProofVerifier::<L, _, _, PallasParameters, VestaParameters>::init(
            bob_updated_comms[i],
            bob_nullifiers[i],
            nonce,
        );
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

    batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

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
        let mut verifier = AccountStateTransitionProofVerifier::<L, _, _, PallasParameters, VestaParameters>::init(
            alice_updated_comms[i],
            alice_nullifiers[i],
            nonce,
        );
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
        let mut verifier = AccountStateTransitionProofVerifier::<L, _, _, PallasParameters, VestaParameters>::init(
            bob_updated_comms[i],
            bob_nullifiers[i],
            nonce,
        );
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
        &account_tree_params,
        &mut rmc_0,
        &mut rmc_1,
    )
    .unwrap();
    verify_rmc(&rmc_0, &rmc_1).unwrap();

    let verify_rmc_time = start.elapsed();

    println!("total proof size = {} bytes, regular verify time = {:?} and with rmc time = {:?}", settlement_proof_size + alice_proof_size + bob_proof_size, verify_time, verify_rmc_time);
}

#[test]
fn multi_asset_state_transition_different_confs() {
    fn check<const L: usize, const M: usize>(
        num_legs: usize,
        height: usize,
        account_tree_params: &SelRerandParameters<PallasParameters, VestaParameters>,
        account_comm_key: impl AccountCommitmentKeyTrait<PallasA> + Clone,
        enc_key_gen: PallasA,
        enc_gen: PallasA,
    ) {
        let mut rng = rand::thread_rng();

        let (((sk_alice, pk_alice), (_, pk_alice_e)), ((sk_bob, pk_bob), (_, pk_bob_e)), (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let keys = vec![(true, pk_auditor_e.0)];

        // Create legs, all with same sender (Alice) and receiver (Bob) but different assets
        let mut leg_encs = Vec::with_capacity(num_legs);
        let mut leg_enc_rands = Vec::with_capacity(num_legs);
        let amount = 100;

        for asset_id in 1..=num_legs as u32 {
            let leg = Leg::new(pk_bob.0, pk_alice.0, keys.clone(), amount, asset_id).unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt::<_, Blake2b512>(&mut rng, pk_bob_e.0, pk_alice_e.0, enc_key_gen, enc_gen)
                .unwrap();
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
            let updated_account = alice_accounts[i]
                .get_state_for_receive();
            let updated_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            alice_updated_comms.push(updated_comm);

            let mut builder = AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
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

        println!("Alice (receive affirmation): {alice_proof_size} bytes and time = {:?}", alice_proving_time);

        let start = Instant::now();

        // Setup verifiers for Alice
        let mut alice_verifiers = Vec::new();
        for i in 0..num_legs {
            let mut verifier = AccountStateTransitionProofVerifier::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_updated_comms[i],
                alice_nullifiers[i],
                nonce,
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

        batch_verify_bp(even_tuples, odd_tuples, account_tree_params).unwrap();

        let verify_time = start.elapsed();

        let start = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let mut alice_verifiers = Vec::new();
        for i in 0..num_legs {
            let mut verifier = AccountStateTransitionProofVerifier::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_updated_comms[i],
                alice_nullifiers[i],
                nonce,
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
            account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verify_rmc_time = start.elapsed();

        println!("Regular verify time = {:?} and with rmc time = {:?}", verify_time, verify_rmc_time);
    }

    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) = setup_gens::<{ 1 << 19 }>(b"test");

    check::<512, 2>(8, 4, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
    check::<512, 4>(8, 4, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
    check::<1024, 2>(8, 3, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
    check::<1024, 4>(8, 3, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
    check::<2000, 2>(8, 3, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
    check::<2000, 4>(8, 3, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
    check::<2048, 2>(8, 3, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
    check::<2048, 4>(8, 3, &account_tree_params, account_comm_key.clone(), enc_key_gen, enc_gen);
}

// Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

#[cfg(feature = "ignore_prover_input_sanitation")]
mod input_sanitation_disabled {
    use crate::account::tests::*;
    use state::AccountCommitmentKeyTrait;

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

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
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
            ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
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

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
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
            ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
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

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
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

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
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

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
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
