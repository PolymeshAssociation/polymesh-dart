#![allow(deprecated)]

use crate::account::state_transition::{
    AccountStateTransitionProofBuilder, AccountStateTransitionProofVerifier,
};
use crate::account::state_transition_multi::MultiAssetStateTransitionProof;
use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, AccountTxnWitness,
    AffirmAsReceiverSplitProof, AffirmAsReceiverSplitProtocol, AffirmAsSenderSplitProof,
    AffirmAsSenderSplitProtocol, ClaimReceivedSplitProof, ClaimReceivedSplitProtocol,
    IrreversibleAffirmAsReceiverSplitProof, IrreversibleAffirmAsReceiverSplitProtocol,
    IrreversibleAffirmAsSenderSplitProof, IrreversibleAffirmAsSenderSplitProtocol,
    ReceiverCounterUpdateSplitProof, ReceiverCounterUpdateSplitProtocol,
    SenderCounterUpdateSplitProof, SenderCounterUpdateSplitProtocol, SenderReverseSplitProof,
    SenderReverseSplitProtocol,
};
use crate::account::{
    AffirmAsReceiverTxnProof, AffirmAsSenderTxnProof, ClaimReceivedTxnProof,
    IrreversibleAffirmAsReceiverTxnProof, IrreversibleAffirmAsSenderTxnProof,
    ReceiverCounterUpdateTxnProof, SenderCounterUpdateTxnProof, SenderReverseTxnProof,
};
use crate::account_registration::tests::{new_account, setup_comm_key};
use crate::auth_proofs::account::AuthProofAffirmation;
use crate::auth_proofs::leg::{LegProverConfig, LegVerifierConfig};
use crate::keys::{DecKey, SigKey, keygen_sig};
use crate::leg::leg_proof::LegCreationProof;
use crate::leg::mediator::MEDIATOR_TXN_LABEL;
use crate::leg::public_asset_leg_proof::{
    PUBLIC_ASSET_LEG_PROOF_TXN_LABEL, PublicAssetLegCreationProof,
};
use crate::leg::settlement_proof::SettlementCreationProof;
use crate::leg::tests::setup_keys;
use crate::leg::{
    AssetCommitmentParams, AssetData, LEG_TXN_EVEN_LABEL, LegEncryption, LegEncryptionRandomness,
};
use crate::leg::{LEG_TXN_ODD_LABEL, LegEncConfig, MediatorTxnProof};
use crate::leg::{
    Leg, LegEncryptionCore, PartyEphemeralPublicKey, ReceiverEphemeralPublicKey,
    SenderEphemeralPublicKey,
};
use crate::util::{
    add_verification_tuples_batches_to_rmc, batch_verify_bp, get_verification_tuples_with_rng,
    prove_with_rng, verify_given_verification_tuples, verify_rmc, verify_with_rng,
};
use crate::{TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL, error::Result};
use ark_ec::CurveGroup;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_pallas::{Affine as PallasA, Fr as PallasFr, PallasConfig as PallasParameters};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_vesta::{Fr as VestaFr, VestaConfig as VestaParameters};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier, verify_given_verification_tuple};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::curve_tree::{CurveTree, Root};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::{SelRerandParametersRef, SelRerandProofParametersNew};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance};
use rand_core::CryptoRngCore;
use std::time::Instant;

#[test]
fn send_txn() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id = 1;
    let amount = 100;

    // Sender account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    // Assume that account had some balance. Either got it as the issuer or from another transfer
    account.balance = 200;

    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();

    let mut test_with_config = |reveal_asset_id: bool| {
        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Setup ends. Sender and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        println!(
            "reveal_asset_id={}, L={L}, height={}",
            reveal_asset_id,
            account_tree.height()
        );
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    };

    // asset-id hidden
    test_with_config(false);

    // asset-id revealed
    test_with_config(true);
}

#[test]
fn affirmation_rejects_substituted_leg_enc() {
    // leg_enc is folded into the affirmation transcript, so a valid sender affirmation for one leg
    // must not verify against a different leg's encryption.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id = 1;
    let amount = 100;

    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 200;
    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();

    let conf = LegEncConfig {
        parties_see_each_other: true,
        reveal_asset_id: false,
    };
    let (_, leg_enc_a, _) = setup_leg_with_conf(
        &mut rng,
        conf.clone(),
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (_, leg_enc_b, _) = setup_leg_with_conf(
        &mut rng,
        conf,
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    let nonce = b"test-nonce";
    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
        &mut rng,
        {
            let (c, e) = leg_enc_a.core_and_eph_keys_for_sender();
            (c, e, amount)
        },
        AccountTxnWitness::new(
            sk_s.0,
            sk_s_e.0,
            account.clone(),
            updated_account.clone(),
            updated_account_comm,
        ),
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
    )
    .unwrap();

    // Sanity: verifies against its own leg.
    proof
        .verify(
            &mut rng,
            leg_enc_a.core_and_eph_keys_for_sender(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            None,
        )
        .unwrap();

    // A different leg's encryption must be rejected.
    assert!(
        proof
            .verify(
                &mut rng,
                leg_enc_b.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                None,
            )
            .is_err()
    );
}

#[test]
fn receive_txn() {
    let mut rng = rand::thread_rng();

    // Setup beings

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id = 1;
    let amount = 100;

    // Receiver account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    // Assume that account had some balance. Either got it as the issuer or from another transfer
    account.balance = 200;
    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();

    let mut test_with_config = |reveal_asset_id: bool| {
        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Setup ends. Receiver and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_receive();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        println!(
            "reveal_asset_id={}, L={L}, height={}",
            reveal_asset_id,
            account_tree.height()
        );
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    };

    // asset-id hidden
    test_with_config(false);

    // asset-id revealed
    test_with_config(true);
}

#[test]
fn claim_received_funds() {
    // This is what report calls txn_cu (counter update) done by receiver
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id = 1;
    let amount = 100;

    // Receiver account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    // Assume that account had some balance and it had sent the receive transaction to increase its counter
    account.balance = 200;
    account.counter += 1;

    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();

    let mut test_with_config = |reveal_asset_id: bool| {
        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Setup ends. Receiver and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_claiming_received(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = ClaimReceivedTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        println!(
            "reveal_asset_id={}, total proof size = {}",
            reveal_asset_id,
            proof.compressed_size()
        );
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    };

    // Test with asset-id hidden
    test_with_config(false);
    // Test with asset-id revealed
    test_with_config(true);
}

#[test]
fn counter_update_txn_by_sender() {
    // This is similar to receive txn as only account's counter is decreased, balance remains same.

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id = 1;
    let amount = 100;

    // Sender account with non-zero counter
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 50;
    account.counter = 1;

    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();

    let mut test_with_config = |reveal_asset_id: bool| {
        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Setup ends. Sender and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = SenderCounterUpdateTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        println!(
            "reveal_asset_id={}, total proof size = {}",
            reveal_asset_id,
            proof.compressed_size()
        );
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    };

    // Test with asset-id hidden
    test_with_config(false);
    // Test with asset-id revealed
    test_with_config(true);
}

#[test]
fn reverse_send_txn() {
    // Sender rolls back a pending send: decrements its counter AND restores the locked amount back into balance.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id = 1;
    let amount = 100;

    // Sender account
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    // Assume that account had some balance and it had sent the send transaction to increase its counter
    account.balance = 200;
    account.counter += 1;

    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();

    let mut test_with_config = |reveal_asset_id: bool| {
        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Setup ends. Sender and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_reversing_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = SenderReverseTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        println!(
            "reveal_asset_id={}, total proof size = {}",
            reveal_asset_id,
            proof.compressed_size()
        );
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    };

    // Test with asset-id hidden
    test_with_config(false);
    // Test with asset-id revealed
    test_with_config(true);
}

#[test]
fn reverse_receive_txn() {
    // This is similar to receive txn as only account's counter is decreased, balance remains same.

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // All parties generate their keys
    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id = 1;
    let amount = 100;

    // Receiver account with non-zero counter
    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    account.balance = 50;
    account.counter = 1;

    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();

    let mut test_with_config = |reveal_asset_id: bool| {
        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Setup ends. Receiver and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) =
            ReceiverCounterUpdateTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    account.clone(),
                    updated_account.clone(),
                    updated_account_comm,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        println!(
            "reveal_asset_id={}, total proof size = {}",
            reveal_asset_id,
            proof.compressed_size()
        );
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    };

    // Test with asset-id hidden
    test_with_config(false);
    // Test with asset-id revealed
    test_with_config(true);
}

#[test]
fn single_shot_settlement() {
    // One leg settled irreversibly in a single round: leg-creation + Irreversible sender + Irreversible receiver
    // proofs all built and batch-verified together (no separate affirm-then-claim steps, no reversal possible).
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;

    let asset_tree_height = 4;
    let account_tree_height = 6;

    let (
        asset_data,
        asset_path,
        asset_tree_root,
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
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
    let settlement_proof =
        LegCreationProof::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>::new::<
            _,
            PallasParams,
            VestaParams,
        >(
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
            account_comm_key.sk_enc_gen(),
            enc_gen,
        )
        .unwrap();
    println!("Settlement creation time : {:?}", start.elapsed());

    let start = Instant::now();
    let (sender_proof, sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                sender_account.clone(),
                updated_sender_account.clone(),
                updated_sender_account_comm,
            ),
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();
    println!("Sender time : {:?}", start.elapsed());

    let start = Instant::now();
    let (receiver_proof, receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                receiver_account.clone(),
                updated_receiver_account.clone(),
                updated_receiver_account_comm,
            ),
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    println!("tuples time : {:?}", start.elapsed());

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
    println!("Verifier time: {:?}", verifier_time);

    let start = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    let (settlement_even, settlement_odd) = settlement_proof
        .verify_and_return_tuples(
            leg_enc.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
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
        &mut rmc_1,
        &mut rmc_0,
    )
    .unwrap();
    verify_rmc(rmc_0, rmc_1).unwrap();
    let verifier_rmc_time = start.elapsed();

    let settlement_proof_size = settlement_proof.compressed_size() + leg_enc.compressed_size();
    let sender_proof_size = sender_proof.compressed_size();
    let receiver_proof_size = receiver_proof.compressed_size();

    println!(
        "Settlement proof size = {} bytes, Sender proof size = {} bytes, Receiver proof size = {} bytes",
        settlement_proof_size, sender_proof_size, receiver_proof_size
    );
    println!(
        "Verifier time = {:?}, Verifier RMC time = {:?}",
        verifier_time, verifier_rmc_time
    );
}

#[test]
fn single_shot_combined_create_and_send() {
    // Folds leg-creation + Irreversible-sender into ONE shared prover/aggregated R1CS proof; the receiver proof
    // is still built separately. Verified via shared verifier for the combined pair plus a tuple for the receiver.
    const NUM_GENS: usize = 1 << 16;
    const L: usize = 64;

    let asset_tree_height = 4;
    let account_tree_height = 6;

    let (
        asset_data,
        asset_path,
        asset_tree_root,
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
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
        enc_gen,
    ) = setup_single_leg_settlement::<NUM_GENS, L>(asset_tree_height, account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"single_shot_combined_nonce_txn_id_1";

    let start = Instant::now();

    let (mut even_prover, mut odd_prover) = create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let leg_creation_proof = LegCreationProof::<
        L,
        PallasFr,
        VestaFr,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover::<_, PallasParams, VestaParams>(
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
        account_comm_key.sk_enc_gen(),
        enc_gen,
        &mut even_prover,
        &mut odd_prover,
    )
    .unwrap();

    let (sender_proof, sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                sender_account.clone(),
                updated_sender_account.clone(),
                updated_sender_account_comm,
            ),
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    let (receiver_proof, receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                receiver_account.clone(),
                updated_receiver_account.clone(),
                updated_receiver_account_comm,
            ),
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

    let receiver_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    println!("Verification time: {:?}", verification_time);

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut odd_verifier,
            &mut even_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (even_tuple, odd_tuple) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            Some(&mut rmc_1),
        )
        .unwrap();

    let even_tuples = vec![odd_tuple, receiver_even];
    let odd_tuples = vec![even_tuple, receiver_odd];

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

    verify_rmc(rmc_0, rmc_1).unwrap();

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

#[test]
fn single_shot_combined_create_and_recv() {
    // Mirror of combined_create_and_send: folds leg-creation + Irreversible-RECEIVER into one shared/aggregated
    // proof, with the sender proof built separately.
    const NUM_GENS: usize = 1 << 14;
    const L: usize = 64;

    let asset_tree_height = 4;
    let account_tree_height = 6;

    let (
        asset_data,
        asset_path,
        asset_tree_root,
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
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
        enc_gen,
    ) = setup_single_leg_settlement::<NUM_GENS, L>(asset_tree_height, account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"single_shot_combined_recv_nonce_txn_id_1";

    let start = Instant::now();

    let (mut even_prover, mut odd_prover) = create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let leg_creation_proof = LegCreationProof::<
        L,
        PallasFr,
        VestaFr,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover::<_, PallasParams, VestaParams>(
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
        account_comm_key.sk_enc_gen(),
        enc_gen,
        &mut even_prover,
        &mut odd_prover,
    )
    .unwrap();

    let (receiver_proof, receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover::<
            _,
            PallasParams,
            VestaParams,
        >(
            &mut rng,
            { let (c, e) = leg_enc.core_and_eph_keys_for_receiver(); (c, e, amount) },
            AccountTxnWitness::new(sk_r.0, sk_r_e.0, receiver_account.clone(), updated_receiver_account.clone(), updated_receiver_account_comm),
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut odd_prover,
            &mut even_prover
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

    let (sender_proof, sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                sender_account.clone(),
                updated_sender_account.clone(),
                updated_sender_account_comm,
            ),
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

    let sender_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    println!("tuples time : {:?}", start.elapsed());

    println!(
        "tuples count {} {} {} {}",
        odd_tuple.proof_dependent_points.len() + sender_even.proof_dependent_points.len(),
        odd_tuple.fixed_point_scalars.len() + sender_odd.fixed_point_scalars.len(),
        even_tuple.proof_dependent_points.len() + sender_odd.proof_dependent_points.len(),
        even_tuple.fixed_point_scalars.len() + sender_odd.fixed_point_scalars.len(),
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

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    verify_rmc(rmc_0, rmc_1).unwrap();

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

#[test]
fn single_shot_swap() {
    // Atomic 2-leg swap done irreversibly in one shot: Alice sends asset1 to Bob, Bob sends asset2 to Alice; each
    // party's two roles (one send, one receive, different assets) are folded into a single combined proof.
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 14;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // Create asset tree params by swapping even/odd from account tree params
    let asset_tree_params = SelRerandProofParametersNew::<
        VestaParameters,
        PallasParameters,
        VestaParams,
        PallasParams,
    >::new(NUM_GENS as u32, NUM_GENS as u32)
    .unwrap();

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        0,
        &account_tree_params.odd_parameters.bp_gens(),
    );

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    let keys = vec![pk_a_e.0];
    let asset_data_1 =
        AssetData::new(asset_id_1, keys.clone(), vec![], &asset_comm_params).unwrap();
    let asset_data_2 =
        AssetData::new(asset_id_2, keys.clone(), vec![], &asset_comm_params).unwrap();

    let set = vec![asset_data_1.commitment, asset_data_2.commitment];
    let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
        &set,
        &asset_tree_params,
        Some(4),
    );
    let asset_path_1 = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_path_2 = asset_tree.get_path_to_leaf_for_proof(1, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    // Create two legs for swap
    let (leg_1, leg_enc_1, leg_enc_rand_1) = setup_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_2, leg_enc_2, leg_enc_rand_2) = setup_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_1.balance = 200;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _, _) =
        new_account(&mut rng, asset_id_2, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_2.balance = 50;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_r.clone(), pk_r_e.clone(), bob_id);
    bob_account_1.balance = 50;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _, _) =
        new_account(&mut rng, asset_id_2, pk_r.clone(), pk_r_e.clone(), bob_id);
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
        Some(6),
    );
    let account_tree_root = account_tree.root_node();

    // Prepare updated account states for irreversible swap (no counter changes)
    let updated_alice_account_1 = alice_account_1
        .get_state_for_irreversible_send(amount_1)
        .unwrap();
    let updated_alice_account_comm_1 = updated_alice_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_alice_account_2 = alice_account_2
        .get_state_for_irreversible_receive(amount_2)
        .unwrap();
    let updated_alice_account_comm_2 = updated_alice_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    let updated_bob_account_1 = bob_account_1
        .get_state_for_irreversible_receive(amount_1)
        .unwrap();
    let updated_bob_account_comm_1 = updated_bob_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0).unwrap();

    let updated_bob_account_2 = bob_account_2
        .get_state_for_irreversible_send(amount_2)
        .unwrap();
    let updated_bob_account_comm_2 = updated_bob_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0).unwrap();

    let nonce = b"single_shot_swap_nonce_txn_id_1";

    let start = Instant::now();

    // Combined settlement proofs for both legs
    let (mut even_prover_settlement, mut odd_prover_settlement) = create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof_1 = LegCreationProof::<
        L,
        PallasFr,
        VestaFr,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover::<_, PallasParams, VestaParams>(
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
        account_comm_key.sk_enc_gen(),
        enc_gen,
        &mut even_prover_settlement,
        &mut odd_prover_settlement,
    )
    .unwrap();

    let settlement_proof_2 = LegCreationProof::<
        L,
        PallasFr,
        VestaFr,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover::<_, PallasParams, VestaParams>(
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
        account_comm_key.sk_enc_gen(),
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

    let proving_setup_time = start.elapsed();
    let start = Instant::now();

    // Combined proofs for Alice (sending in leg1, receiving in leg2)
    let (mut even_prover_alice, mut odd_prover_alice) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (alice_sender_proof, alice_sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc_1.core_and_eph_keys_for_sender();
                (c, e, amount_1)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_1.clone(),
                updated_alice_account_1.clone(),
                updated_alice_account_comm_1,
            ),
            alice_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    let (alice_receiver_proof, alice_receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover::<
            _,
            PallasParams,
            VestaParams,
        >(
            &mut rng,
            (leg_enc_2.leg_enc_core_and_eph_keys.core.clone(), leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(), amount_2),
            AccountTxnWitness::new(sk_s.0, sk_s_e.0, alice_account_2.clone(), updated_alice_account_2.clone(), updated_alice_account_comm_2),
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice
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

    let proving_alice_time = start.elapsed();
    let start = Instant::now();

    // Combined proofs for Bob (receiving in leg1, sending in leg2)
    let (mut even_prover_bob, mut odd_prover_bob) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (bob_receiver_proof, bob_receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover::<
            _,
            PallasParams,
            VestaParams,
        >(
            &mut rng,
            (leg_enc_1.leg_enc_core_and_eph_keys.core.clone(), leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(), amount_1),
            AccountTxnWitness::new(sk_r.0, sk_r_e.0, bob_account_1.clone(), updated_bob_account_1.clone(), updated_bob_account_comm_1),
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob
        )
        .unwrap();

    let (bob_sender_proof, bob_sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_2.clone(),
                updated_bob_account_2.clone(),
                updated_bob_account_comm_2,
            ),
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    let proving_bob_time = start.elapsed();
    let start = Instant::now();

    // Verify all proofs
    let (mut settlement_even_verifier, mut settlement_odd_verifier) =
        create_verifiers::<VestaParameters, PallasParameters>(
            LEG_TXN_EVEN_LABEL,
            LEG_TXN_ODD_LABEL,
        );

    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    // Verify Settlement Proofs
    settlement_proof_1
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_1.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    settlement_proof_2
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_2.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut settlement_even_verifier,
            &mut settlement_odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    // Get tuples for settlement
    let (settlement_even_tuple, settlement_odd_tuple) = get_verification_tuples_with_rng(
        settlement_odd_verifier,
        settlement_even_verifier,
        &settlement_odd_bp,
        &settlement_even_bp,
        &mut rng,
    )
    .unwrap();

    // Verify Alice Proofs
    let (mut alice_even_verifier, mut alice_odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    alice_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (alice_even_tuple, alice_odd_tuple) = get_verification_tuples_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        &mut rng,
    )
    .unwrap();

    // Verify Bob Proofs
    let (mut bob_even_verifier, mut bob_odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    bob_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    let (bob_even_tuple, bob_odd_tuple) = get_verification_tuples_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        &mut rng,
    )
    .unwrap();

    let even_tuples = vec![settlement_even_tuple, alice_even_tuple, bob_even_tuple];

    let odd_tuples = vec![settlement_odd_tuple, alice_odd_tuple, bob_odd_tuple];

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

    verify_rmc(rmc_0, rmc_1).unwrap();

    let verification_time = start.elapsed();
    println!("Total verification time: {:?}", verification_time);

    let settlement_proof_size = leg_enc_1.compressed_size()
        + leg_enc_2.compressed_size()
        + settlement_proof_1.compressed_size()
        + settlement_proof_2.compressed_size()
        + settlement_even_bp.compressed_size()
        + settlement_odd_bp.compressed_size();
    let alice_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_sender_proof.compressed_size()
        + alice_receiver_proof.compressed_size();
    let bob_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_receiver_proof.compressed_size()
        + bob_sender_proof.compressed_size();

    println!(
        "Settlement proof size = {} bytes, Alice proof size = {} bytes, Bob proof size = {} bytes",
        settlement_proof_size, alice_proof_size, bob_proof_size
    );
    println!(
        "Proving setup time = {:?}, Alice proving time = {:?}, Bob proving time = {:?}",
        proving_setup_time, proving_alice_time, proving_bob_time
    );
}

#[test]
fn single_shot_settlement_asset_id_revealed() {
    // Same single-shot irreversible settlement as single_shot_settlement, but the asset-id is public, so it uses
    // PublicAssetLegCreationProof (no asset curve-tree / membership proof) instead of LegCreationProof.
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;

    let account_tree_height = 6;

    let (
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
        updated_sender_account,
        updated_receiver_account,
        updated_sender_account_comm,
        updated_receiver_account_comm,
        sender_path,
        receiver_path,
        account_tree_root,
        account_tree_params,
        account_comm_key,
        enc_gen,
    ) = setup_single_leg_settlement_public_asset::<NUM_GENS, L>(account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"single_shot_settlement_public_asset_nonce_1";

    let leaf_level_pc_gens = PedersenGens::<Affine<PallasParameters>>::default();
    let leaf_level_bp_gens = BulletproofGens::<Affine<PallasParameters>>::new(NUM_GENS as u32, 1);

    println!("For L={L}, account tree height = {account_tree_height}, asset_id revealed");

    // Create all three proofs
    let start = Instant::now();
    let settlement_proof = PublicAssetLegCreationProof::<PallasParameters>::new(
        &mut rng,
        leg.clone(),
        leg_enc.clone(),
        leg_enc_rand.clone(),
        nonce,
        &leaf_level_pc_gens,
        &leaf_level_bp_gens,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    )
    .unwrap();
    println!("Settlement creation time : {:?}", start.elapsed());

    let start = Instant::now();
    let (sender_proof, sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                sender_account.clone(),
                updated_sender_account.clone(),
                updated_sender_account_comm,
            ),
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();
    println!("Sender time : {:?}", start.elapsed());

    let start = Instant::now();
    let (receiver_proof, receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                receiver_account.clone(),
                updated_receiver_account.clone(),
                updated_receiver_account_comm,
            ),
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();
    println!("Receiver time : {:?}", start.elapsed());

    let start = Instant::now();

    // All 3 can be verified in parallel
    settlement_proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            leg_enc.asset_id().unwrap(),
            vec![leg.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            None,
        )
        .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    println!("tuples time : {:?}", start.elapsed());

    let even_tuples = vec![sender_even, receiver_even];
    let odd_tuples = vec![sender_odd, receiver_odd];

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
    println!("Verifier time: {:?}", verifier_time);

    let settlement_proof_size = settlement_proof.compressed_size() + leg_enc.compressed_size();
    let sender_proof_size = sender_proof.compressed_size();
    let receiver_proof_size = receiver_proof.compressed_size();

    println!(
        "Settlement proof size = {} bytes, Sender proof size = {} bytes, Receiver proof size = {} bytes",
        settlement_proof_size, sender_proof_size, receiver_proof_size
    );
    println!("Verifier time = {:?}", verifier_time);
}

#[test]
fn single_shot_combined_create_and_send_asset_id_revealed() {
    // combined_create_and_send but with public asset-id: leg uses a single-curve PublicAssetLegCreationProof
    // (own prover), folded with the Irreversible-sender's two-curve proof; receiver proof built separately.
    const NUM_GENS: usize = 1 << 16;
    const L: usize = 64;

    let account_tree_height = 6;

    let (
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
        updated_sender_account,
        updated_receiver_account,
        updated_sender_account_comm,
        updated_receiver_account_comm,
        sender_path,
        receiver_path,
        account_tree_root,
        account_tree_params,
        account_comm_key,
        enc_gen,
    ) = setup_single_leg_settlement_public_asset::<NUM_GENS, L>(account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"combined_create_send_public_asset_nonce_1";

    let leaf_level_pc_gens = PedersenGens::<Affine<PallasParameters>>::default();
    let leaf_level_bp_gens = BulletproofGens::<Affine<PallasParameters>>::new(NUM_GENS as u32, 1);

    let start = Instant::now();

    let transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut leg_prover = Prover::new(&leaf_level_pc_gens, transcript);

    let leg_creation_proof =
        PublicAssetLegCreationProof::<PallasParameters>::new_with_given_prover(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut leg_prover,
        )
        .unwrap();

    let leg_r1cs_proof = leg_prover
        .prove_with_rng(&leaf_level_bp_gens, &mut rng)
        .unwrap();

    let (mut even_prover, mut odd_prover) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (sender_proof, sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                sender_account.clone(),
                updated_sender_account.clone(),
                updated_sender_account_comm,
            ),
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )
        .unwrap();

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let proving_time = start.elapsed();

    let start = Instant::now();

    let (receiver_proof, receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                receiver_account.clone(),
                updated_receiver_account.clone(),
                updated_receiver_account_comm,
            ),
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

    let receiver_proving_time = start.elapsed();

    let start = Instant::now();

    let mut leg_creation_proof = leg_creation_proof;
    leg_creation_proof.r1cs_proof = Some(leg_r1cs_proof.clone());

    let verifier_transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut leg_verifier = Verifier::new(verifier_transcript);

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            leg_enc.asset_id().unwrap(),
            vec![leg.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut leg_verifier,
            None,
        )
        .unwrap();

    leg_verifier
        .verification_scalars_and_points_with_rng(&leg_r1cs_proof, &mut rng)
        .and_then(|tuple| {
            verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens)
        })
        .unwrap();

    let (mut even_verifier, mut odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    let (even_tuple, odd_tuple) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let (receiver_even, receiver_odd) = receiver_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let even_tuples = vec![even_tuple, receiver_even];
    let odd_tuples = vec![odd_tuple, receiver_odd];

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

    println!(
        "Total proof size = {}",
        leg_r1cs_proof.compressed_size()
            + leg_enc.compressed_size()
            + leg_creation_proof.compressed_size()
            + even_bp.compressed_size()
            + odd_bp.compressed_size()
            + sender_proof.compressed_size()
            + receiver_proof.compressed_size()
    );
    println!(
        "Combined (settlement + sender): proving time = {:?}",
        proving_time
    );
    println!("Receiver: proving time = {:?}", receiver_proving_time);
    println!("verification time = {:?}", verification_time);
}

#[test]
fn single_shot_combined_create_and_recv_asset_id_revealed() {
    // combined_create_and_recv but with public asset-id: single-curve PublicAssetLegCreationProof folded with the
    // Irreversible-RECEIVER's two-curve proof; sender proof built separately.
    const NUM_GENS: usize = 1 << 14;
    const L: usize = 64;

    let account_tree_height = 6;

    let (
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
        updated_sender_account,
        updated_receiver_account,
        updated_sender_account_comm,
        updated_receiver_account_comm,
        sender_path,
        receiver_path,
        account_tree_root,
        account_tree_params,
        account_comm_key,
        enc_gen,
    ) = setup_single_leg_settlement_public_asset::<NUM_GENS, L>(account_tree_height);

    let mut rng = rand::thread_rng();
    let amount = 50;

    let nonce = b"combined_create_recv_public_asset_nonce_1";

    let leaf_level_pc_gens = PedersenGens::<Affine<PallasParameters>>::default();
    let leaf_level_bp_gens = BulletproofGens::<Affine<PallasParameters>>::new(NUM_GENS as u32, 1);

    let start = Instant::now();

    let transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut leg_prover = Prover::new(&leaf_level_pc_gens, transcript);

    let leg_creation_proof =
        PublicAssetLegCreationProof::<PallasParameters>::new_with_given_prover(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut leg_prover,
        )
        .unwrap();

    let leg_r1cs_proof = leg_prover
        .prove_with_rng(&leaf_level_bp_gens, &mut rng)
        .unwrap();

    let (mut even_prover, mut odd_prover) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (receiver_proof, receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover::<
            _,
            PallasParams,
            VestaParams,
        >(
            &mut rng,
            { let (c, e) = leg_enc.core_and_eph_keys_for_receiver(); (c, e, amount) },
            AccountTxnWitness::new(sk_r.0, sk_r_e.0, receiver_account.clone(), updated_receiver_account.clone(), updated_receiver_account_comm),
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover,
            &mut odd_prover
        )
        .unwrap();

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        account_tree_params.even_parameters.bp_gens(),
        account_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();

    let proving_time = start.elapsed();

    let start = Instant::now();

    let (sender_proof, sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                sender_account.clone(),
                updated_sender_account.clone(),
                updated_sender_account_comm,
            ),
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

    let sender_proving_time = start.elapsed();

    let start = Instant::now();

    let mut leg_creation_proof = leg_creation_proof;
    leg_creation_proof.r1cs_proof = Some(leg_r1cs_proof.clone());

    let verifier_transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut leg_verifier = Verifier::new(verifier_transcript);

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            leg_enc.asset_id().unwrap(),
            vec![leg.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut leg_verifier,
            None,
        )
        .unwrap();

    leg_verifier
        .verification_scalars_and_points_with_rng(&leg_r1cs_proof, &mut rng)
        .and_then(|tuple| {
            verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens)
        })
        .unwrap();

    let (mut even_verifier, mut odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            updated_receiver_account_comm,
            receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    let (even_tuple, odd_tuple) =
        get_verification_tuples_with_rng(even_verifier, odd_verifier, &even_bp, &odd_bp, &mut rng)
            .unwrap();

    let (sender_even, sender_odd) = sender_proof
        .verify_and_return_tuples(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_sender_account_comm,
            sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut rng,
            None,
        )
        .unwrap();

    let even_tuples = vec![even_tuple, sender_even];
    let odd_tuples = vec![odd_tuple, sender_odd];

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

    println!("For L={L}, account tree height={account_tree_height}, asset_id revealed");

    println!(
        "Total proof size = {}",
        leg_r1cs_proof.compressed_size()
            + leg_enc.compressed_size()
            + leg_creation_proof.compressed_size()
            + even_bp.compressed_size()
            + odd_bp.compressed_size()
            + receiver_proof.compressed_size()
            + sender_proof.compressed_size()
    );
    println!(
        "Combined (settlement + receiver): proving time = {:?}",
        proving_time
    );
    println!("Sender: proving time = {:?}", sender_proving_time);
    println!("verification time = {:?}", verification_time);
}

#[test]
fn single_shot_swap_asset_id_revealed() {
    // single_shot_swap (atomic Alice<->Bob 2-asset swap, irreversible) but with public asset-ids: each leg uses a
    // single-curve PublicAssetLegCreationProof, no asset curve tree.
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 14;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) =
        setup_gens_new::<NUM_GENS>(b"testing_swap_public_asset");

    let leaf_level_pc_gens = PedersenGens::<Affine<PallasParameters>>::default();
    let leaf_level_bp_gens = BulletproofGens::<Affine<PallasParameters>>::new(NUM_GENS as u32, 1);

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Create two legs for swap (both with revealed asset_id)
    let (leg_1, leg_enc_1, leg_enc_rand_1) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_2, leg_enc_2, leg_enc_rand_2) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_1.balance = 200;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _, _) =
        new_account(&mut rng, asset_id_2, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_2.balance = 50;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_r.clone(), pk_r_e.clone(), bob_id);
    bob_account_1.balance = 50;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _, _) =
        new_account(&mut rng, asset_id_2, pk_r.clone(), pk_r_e.clone(), bob_id);
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
        Some(6),
    );
    let account_tree_root = account_tree.root_node();

    // Prepare updated account states for irreversible swap (no counter changes)
    let updated_alice_account_1 = alice_account_1
        .get_state_for_irreversible_send(amount_1)
        .unwrap();
    let updated_alice_account_comm_1 = updated_alice_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_alice_account_2 = alice_account_2
        .get_state_for_irreversible_receive(amount_2)
        .unwrap();
    let updated_alice_account_comm_2 = updated_alice_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    let updated_bob_account_1 = bob_account_1
        .get_state_for_irreversible_receive(amount_1)
        .unwrap();
    let updated_bob_account_comm_1 = updated_bob_account_1
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0).unwrap();

    let updated_bob_account_2 = bob_account_2
        .get_state_for_irreversible_send(amount_2)
        .unwrap();
    let updated_bob_account_comm_2 = updated_bob_account_2
        .commit(account_comm_key.clone())
        .unwrap();
    let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0).unwrap();

    let nonce = b"single_shot_swap_public_asset_nonce_1";

    let start = Instant::now();

    // Combined settlement proofs for both legs
    let transcript_1 = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut prover_1 = Prover::new(&leaf_level_pc_gens, transcript_1);

    let settlement_proof_1 =
        PublicAssetLegCreationProof::<PallasParameters>::new_with_given_prover(
            &mut rng,
            leg_1.clone(),
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut prover_1,
        )
        .unwrap();

    let transcript_2 = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut prover_2 = Prover::new(&leaf_level_pc_gens, transcript_2);

    let settlement_proof_2 =
        PublicAssetLegCreationProof::<PallasParameters>::new_with_given_prover(
            &mut rng,
            leg_2.clone(),
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut prover_2,
        )
        .unwrap();

    let settlement_r1cs_proof_1 = prover_1
        .prove_with_rng(&leaf_level_bp_gens, &mut rng)
        .unwrap();
    let settlement_r1cs_proof_2 = prover_2
        .prove_with_rng(&leaf_level_bp_gens, &mut rng)
        .unwrap();

    let proving_setup_time = start.elapsed();
    let start = Instant::now();

    // Combined proofs for Alice (sending in leg1, receiving in leg2)
    let (mut even_prover_alice, mut odd_prover_alice) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (alice_sender_proof, alice_sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc_1.core_and_eph_keys_for_sender();
                (c, e, amount_1)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_1.clone(),
                updated_alice_account_1.clone(),
                updated_alice_account_comm_1,
            ),
            alice_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    let (alice_receiver_proof, alice_receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover::<
            _,
            PallasParams,
            VestaParams,
        >(
            &mut rng,
            (leg_enc_2.leg_enc_core_and_eph_keys.core.clone(), leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(), amount_2),
            AccountTxnWitness::new(sk_s.0, sk_s_e.0, alice_account_2.clone(), updated_alice_account_2.clone(), updated_alice_account_comm_2),
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice
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

    let proving_alice_time = start.elapsed();
    let start = Instant::now();

    // Combined proofs for Bob (receiving in leg1, sending in leg2)
    let (mut even_prover_bob, mut odd_prover_bob) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (bob_receiver_proof, bob_receiver_nullifier) =
        IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover::<
            _,
            PallasParams,
            VestaParams,
        >(
            &mut rng,
            (leg_enc_1.leg_enc_core_and_eph_keys.core.clone(), leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(), amount_1),
            AccountTxnWitness::new(sk_r.0, sk_r_e.0, bob_account_1.clone(), updated_bob_account_1.clone(), updated_bob_account_comm_1),
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob
        )
        .unwrap();

    let (bob_sender_proof, bob_sender_nullifier) =
        IrreversibleAffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_2.clone(),
                updated_bob_account_2.clone(),
                updated_bob_account_comm_2,
            ),
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    let proving_bob_time = start.elapsed();
    let start = Instant::now();

    // Verify Settlement Proofs
    let mut settlement_proof_1 = settlement_proof_1;
    settlement_proof_1.r1cs_proof = Some(settlement_r1cs_proof_1.clone());

    settlement_proof_1
        .verify(
            &mut rng,
            leg_enc_1.clone(),
            leg_enc_1.asset_id().unwrap(),
            vec![leg_1.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            None,
        )
        .unwrap();

    let mut settlement_proof_2 = settlement_proof_2;
    settlement_proof_2.r1cs_proof = Some(settlement_r1cs_proof_2.clone());

    settlement_proof_2
        .verify(
            &mut rng,
            leg_enc_2.clone(),
            leg_enc_2.asset_id().unwrap(),
            vec![leg_2.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            None,
        )
        .unwrap();

    // Verify Alice Proofs
    let (mut alice_even_verifier, mut alice_odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    let (alice_even_tuple, alice_odd_tuple) = get_verification_tuples_with_rng(
        alice_even_verifier,
        alice_odd_verifier,
        &alice_even_bp,
        &alice_odd_bp,
        &mut rng,
    )
    .unwrap();

    // Verify Bob Proofs
    let (mut bob_even_verifier, mut bob_odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_receiver_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_receiver_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_sender_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_sender_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    let (bob_even_tuple, bob_odd_tuple) = get_verification_tuples_with_rng(
        bob_even_verifier,
        bob_odd_verifier,
        &bob_even_bp,
        &bob_odd_bp,
        &mut rng,
    )
    .unwrap();

    let even_tuples = vec![alice_even_tuple, bob_even_tuple];
    let odd_tuples = vec![alice_odd_tuple, bob_odd_tuple];

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
    println!("Total verification time: {:?}", verification_time);

    let settlement_proof_size = leg_enc_1.compressed_size()
        + leg_enc_2.compressed_size()
        + settlement_proof_1.compressed_size()
        + settlement_proof_2.compressed_size()
        + settlement_r1cs_proof_1.compressed_size()
        + settlement_r1cs_proof_2.compressed_size();
    let alice_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_sender_proof.compressed_size()
        + alice_receiver_proof.compressed_size();
    let bob_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_receiver_proof.compressed_size()
        + bob_sender_proof.compressed_size();

    println!(
        "Settlement proof size = {} bytes, Alice proof size = {} bytes, Bob proof size = {} bytes",
        settlement_proof_size, alice_proof_size, bob_proof_size
    );
    println!(
        "Proving setup time = {:?}, Alice proving time = {:?}, Bob proving time = {:?}",
        proving_setup_time, proving_alice_time, proving_bob_time
    );
}

#[test]
fn swap_settlement_asset_id_revealed() {
    // swap_settlement (reversible Alice<->Bob 2-asset swap via ordinary affirm proofs, counters bumped) but with
    // public asset-ids, so each leg uses a single-curve PublicAssetLegCreationProof.
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) =
        setup_gens_new::<NUM_GENS>(b"testing_swap_public_asset");

    let leaf_level_pc_gens = PedersenGens::<Affine<PallasParameters>>::default();
    let leaf_level_bp_gens = BulletproofGens::<Affine<PallasParameters>>::new(NUM_GENS as u32, 1);

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    // Two different asset-ids for swap (both revealed)
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Create two legs for swap (both with revealed asset_id)
    let (leg_1, leg_enc_1, leg_enc_rand_1) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_2, leg_enc_2, leg_enc_rand_2) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_1.balance = 200;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _, _) =
        new_account(&mut rng, asset_id_2, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_2.balance = 50;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_r.clone(), pk_r_e.clone(), bob_id);
    bob_account_1.balance = 50;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _, _) = new_account(&mut rng, asset_id_2, pk_r, pk_r_e, bob_id);
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
        Some(6),
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

    let nonce = b"swap_settlement_public_asset_nonce_1";

    // Combined settlement proofs for both legs
    let clock = Instant::now();

    let transcript_1 = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut prover_1 = Prover::new(&leaf_level_pc_gens, transcript_1);

    let settlement_proof_1 =
        PublicAssetLegCreationProof::<PallasParameters>::new_with_given_prover(
            &mut rng,
            leg_1.clone(),
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut prover_1,
        )
        .unwrap();

    let transcript_2 = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
    let mut prover_2 = Prover::new(&leaf_level_pc_gens, transcript_2);

    let settlement_proof_2 =
        PublicAssetLegCreationProof::<PallasParameters>::new_with_given_prover(
            &mut rng,
            leg_2.clone(),
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut prover_2,
        )
        .unwrap();

    let settlement_r1cs_proof_1 = prover_1
        .prove_with_rng(&leaf_level_bp_gens, &mut rng)
        .unwrap();
    let settlement_r1cs_proof_2 = prover_2
        .prove_with_rng(&leaf_level_bp_gens, &mut rng)
        .unwrap();

    let settlement_proving_time = clock.elapsed();

    // Verify settlement proofs (both legs)
    let clock = Instant::now();

    let mut settlement_proof_1 = settlement_proof_1;
    settlement_proof_1.r1cs_proof = Some(settlement_r1cs_proof_1.clone());

    settlement_proof_1
        .verify(
            &mut rng,
            leg_enc_1.clone(),
            leg_enc_1.asset_id().unwrap(),
            vec![leg_1.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            None,
        )
        .unwrap();

    let mut settlement_proof_2 = settlement_proof_2;
    settlement_proof_2.r1cs_proof = Some(settlement_r1cs_proof_2.clone());

    settlement_proof_2
        .verify(
            &mut rng,
            leg_enc_2.clone(),
            leg_enc_2.asset_id().unwrap(),
            vec![leg_2.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            None,
        )
        .unwrap();

    let settlement_verification_time = clock.elapsed();

    // Combined alice proofs for both legs (alice sends in leg1, receives in leg2)
    let clock = Instant::now();
    let (mut even_prover_alice, mut odd_prover_alice) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Alice proof for leg1 (sending asset1)
    let (alice_proof_leg1, alice_nullifier_leg1) =
        AffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc_1.core_and_eph_keys_for_sender();
                (c, e, amount_1)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_1.clone(),
                updated_alice_account_1.clone(),
                updated_alice_account_comm_1,
            ),
            alice_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    // Alice proof for leg2 (receiving asset2)
    let (alice_proof_leg2, alice_nullifier_leg2) =
        AffirmAsReceiverTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_2.clone(),
                updated_alice_account_2.clone(),
                updated_alice_account_comm_2,
            ),
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    let (mut even_prover_bob, mut odd_prover_bob) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Bob proof for leg1 (receiving asset1)
    let (bob_proof_leg1, bob_nullifier_leg1) =
        AffirmAsReceiverTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_1,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_1.clone(),
                updated_bob_account_1.clone(),
                updated_bob_account_comm_1,
            ),
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    // Bob proof for leg2 (sending asset2)
    let (bob_proof_leg2, bob_nullifier_leg2) =
        AffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_2.clone(),
                updated_bob_account_2.clone(),
                updated_bob_account_comm_2,
            ),
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    let settlement_proof_size = leg_enc_1.compressed_size()
        + leg_enc_2.compressed_size()
        + settlement_proof_1.compressed_size()
        + settlement_proof_2.compressed_size()
        + settlement_r1cs_proof_1.compressed_size()
        + settlement_r1cs_proof_2.compressed_size();

    let alice_affirmation_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_proof_leg1.compressed_size()
        + alice_proof_leg2.compressed_size();

    let bob_affirmation_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_proof_leg1.compressed_size()
        + bob_proof_leg2.compressed_size();

    println!("For L={L}, asset_id revealed");
    println!(
        "Settlement proving time = {:?}, verification time = {:?}, proof size = {} bytes",
        settlement_proving_time, settlement_verification_time, settlement_proof_size
    );
    println!(
        "Alice proving time = {:?}, verification time = {:?}, proof size = {} bytes",
        alice_proving_time, alice_verification_time, alice_affirmation_proof_size
    );
    println!(
        "Bob proving time = {:?}, verification time = {:?}, proof size = {} bytes",
        bob_proving_time, bob_verification_time, bob_affirmation_proof_size
    );
}

#[test]
fn reverse_settlement_asset_id_revealed() {
    // reverse_settlement (both parties roll back a 2-leg settlement: sender un-sends, receiver decrements its
    // pending counter) but with public asset-ids; no leg-creation proof, only the per-party reverse/counter proofs.
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) =
        setup_gens_new::<NUM_GENS>(b"testing_reverse_public_asset");

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    // Two different asset-ids for swap (both revealed)
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Create two legs for swap (both with revealed asset_id)
    let (_, leg_enc_1, _) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (_, leg_enc_2, _) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_1.balance = 500;
    alice_account_1.counter = 1;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _, _) =
        new_account(&mut rng, asset_id_2, pk_s.clone(), pk_s_e.clone(), alice_id);
    alice_account_2.balance = 50;
    alice_account_2.counter = 1;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _, _) =
        new_account(&mut rng, asset_id_1, pk_r.clone(), pk_r_e.clone(), bob_id);
    bob_account_1.balance = 500;
    bob_account_1.counter = 1;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _, _) =
        new_account(&mut rng, asset_id_2, pk_r.clone(), pk_r_e.clone(), bob_id);
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
        Some(6),
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

    let nonce = b"reverse_settlement_public_asset_nonce_1";

    // Combined alice proofs for both legs (alice reverses send in leg1, reverses receive in leg2)
    let clock = Instant::now();
    let (mut even_prover_alice, mut odd_prover_alice) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Alice proof for leg1 (reverse sending asset1)
    let (alice_proof_leg1, alice_nullifier_leg1) =
        SenderReverseTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc_1.core_and_eph_keys_for_sender();
                (c, e, amount_1)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_1.clone(),
                updated_alice_account_1.clone(),
                updated_alice_account_comm_1,
            ),
            alice_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    // Alice proof for leg2 (reverse receiving asset2)
    let (alice_proof_leg2, alice_nullifier_leg2) =
        ReceiverCounterUpdateTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_2.clone(),
                updated_alice_account_2.clone(),
                updated_alice_account_comm_2,
            ),
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    let (mut even_prover_bob, mut odd_prover_bob) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Bob proof for leg1 (reverse receiving asset1)
    let (bob_proof_leg1, bob_nullifier_leg1) =
        ReceiverCounterUpdateTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_1,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_1.clone(),
                updated_bob_account_1.clone(),
                updated_bob_account_comm_1,
            ),
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    // Bob proof for leg2 (reverse sending asset2)
    let (bob_proof_leg2, bob_nullifier_leg2) =
        SenderReverseTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_2.clone(),
                updated_bob_account_2.clone(),
                updated_bob_account_comm_2,
            ),
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    let alice_affirmation_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_proof_leg1.compressed_size()
        + alice_proof_leg2.compressed_size();

    let bob_affirmation_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_proof_leg1.compressed_size()
        + bob_proof_leg2.compressed_size();

    println!("For L={L}, asset_id revealed");
    println!(
        "Alice reversing proving time = {:?}, verification time = {:?}, proof size = {} bytes",
        alice_proving_time, alice_verification_time, alice_affirmation_proof_size
    );
    println!(
        "Bob reversing proving time = {:?}, verification time = {:?}, proof size = {} bytes",
        bob_proving_time, bob_verification_time, bob_affirmation_proof_size
    );
}

#[test]
fn batch_send_txn_proofs() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 10;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| {
            setup_keys(
                &mut rng,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
            )
        })
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let ((_sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
        let (_, (_, pk_r_e)) = &all_keys[i].1;
        let ((_, _), (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);

        // Create sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, *pk_s, *pk_s_e, id);
        account.balance = 200; // Ensure sufficient balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(6),
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
        let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount,
            ),
            AccountTxnWitness::new(
                all_keys[i].0.0.0.0,
                all_keys[i].0.1.0.0,
                accounts[i].clone(),
                updated_accounts[i].clone(),
                updated_account_comms[i],
            ),
            paths[i].clone(),
            &root,
            &nonces[i],
            &account_tree_params,
            account_comm_key.clone(),
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
                (
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
                (
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
                (
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();
    let batch_verifier_rmc_time = clock.elapsed();

    println!(
        "For {batch_size} send txn proofs, batch verifier_rmc time {:?}",
        batch_verifier_rmc_time
    );
}

#[test]
fn combined_send_txn_proofs() {
    // 10 send proofs all SHARING one even/odd prover -> a single aggregated R1CS/Bulletproof for all of them
    // (contrast batch_send_txn_proofs, where each proof stays independent and only the mult-check is batched).
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 16; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 10;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| {
            setup_keys(
                &mut rng,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
            )
        })
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let ((_sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
        let (_, (_, pk_r_e)) = &all_keys[i].1;
        let (_, (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);

        // Create sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, *pk_s, *pk_s_e, id);
        account.balance = 200; // Ensure sufficient balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(6),
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
    let (mut even_prover, mut odd_prover) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let mut proofs = Vec::with_capacity(batch_size);
    let mut nullifiers = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let (proof, nullifier) =
            AffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
                &mut rng,
                (
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                    amount,
                ),
                AccountTxnWitness::new(
                    all_keys[i].0.0.0.0,
                    all_keys[i].0.1.0.0,
                    accounts[i].clone(),
                    updated_accounts[i].clone(),
                    updated_account_comms[i],
                ),
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                (
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                (
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();
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
fn combined_create_and_send() {
    // Folds two distinct ops -- leg/settlement-creation (LegCreationProof, hidden asset) + sender affirm -- into
    // one shared prover producing a single aggregated proof (the reversible analogue of single_shot_combined_*).
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 16;
    const L: usize = 64;
    let (account_tree_params, asset_tree_params, _, account_comm_key, enc_gen) =
        setup_asset_and_account_params_new::<NUM_GENS>();

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        1,
        account_tree_params.odd_parameters.bp_gens(),
    );

    let asset_id = 1;
    let amount = 100;

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((_, _), (_, pk_r_e)), (_, (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let (_, pk_m) = keygen_sig(&mut rng, account_comm_key.sk_gen());
    let keys_enc = vec![pk_a_e.0];
    let keys_med = vec![pk_m.0];
    let asset_data = AssetData::new(
        asset_id,
        keys_enc.clone(),
        keys_med.clone(),
        &asset_comm_params,
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

    let (leg, leg_enc, leg_enc_rand) = setup_leg(
        &mut rng,
        pk_a_e.0,
        Some(pk_m.0),
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 200;

    let account_tree = get_tree_with_account_comm::<L, _>(
        &account,
        account_comm_key.clone(),
        &account_tree_params,
        6,
    )
    .unwrap();
    let account_tree_root = account_tree.root_node();

    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let account_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let nonce = b"test_nonce";

    let clock = Instant::now();

    let (mut even_prover, mut odd_prover) = create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let leg_creation_proof =
        LegCreationProof::new_with_given_prover::<_, PallasParams, VestaParams>(
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
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )
        .unwrap();

    let (send_proof, nullifier) =
        AffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            account_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            None,
        )
        .unwrap();

    send_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    leg_creation_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            Some(&mut rmc_1),
        )
        .unwrap();

    send_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

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

#[test]
fn batch_receive_txn_proofs() {
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 5;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| {
            setup_keys(
                &mut rng,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
            )
        })
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let (_, (_, pk_s_e)) = &all_keys[i].0;
        let ((_sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
        let (_, (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);

        // Create receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, *pk_r, *pk_r_e, id);
        account.balance = 200; // Ensure some initial balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(6),
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
        let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_encs[i].core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                all_keys[i].1.0.0.0,
                all_keys[i].1.1.0.0,
                accounts[i].clone(),
                updated_accounts[i].clone(),
                updated_account_comms[i],
            ),
            paths[i].clone(),
            &root,
            &nonces[i],
            &account_tree_params,
            account_comm_key.clone(),
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
                leg_encs[i].core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_encs[i].core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
                leg_encs[i].core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();
    let batch_verifier_rmc_time = clock.elapsed();

    println!(
        "For {batch_size} receive txn proofs, batch verifier_rmc time {:?}",
        batch_verifier_rmc_time
    );
}

#[test]
fn combined_receive_txn_proofs() {
    // Receive analogue of combined_send_txn_proofs: several receive proofs share one prover -> one aggregated proof.
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 15;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let batch_size = 5;

    let mut accounts = Vec::with_capacity(batch_size);
    let mut updated_accounts = Vec::with_capacity(batch_size);
    let mut updated_account_comms = Vec::with_capacity(batch_size);
    let mut paths = Vec::with_capacity(batch_size);
    let mut legs = Vec::with_capacity(batch_size);
    let mut leg_encs = Vec::with_capacity(batch_size);

    // Generate keys for all parties
    let all_keys: Vec<_> = (0..batch_size)
        .map(|_| {
            setup_keys(
                &mut rng,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
            )
        })
        .collect();

    // Create accounts and legs
    let mut account_comms = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let (_, (_sk_s_e, pk_s_e)) = &all_keys[i].0;
        let ((_sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
        let (_, (_, pk_a_e)) = &all_keys[i].2;

        let (leg, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );
        legs.push(leg);
        leg_encs.push(leg_enc);

        // Create receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, *pk_r, *pk_r_e, id);
        account.balance = 200; // Ensure some initial balance
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        accounts.push(account);
        account_comms.push(account_comm);
    }

    let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(6),
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
    let (mut even_prover, mut odd_prover) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let mut proofs = Vec::with_capacity(batch_size);
    let mut nullifiers = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        let (proof, nullifier) =
            AffirmAsReceiverTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_encs[i].core_and_eph_keys_for_receiver();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    all_keys[i].1.0.0.0,
                    all_keys[i].1.1.0.0,
                    accounts[i].clone(),
                    updated_accounts[i].clone(),
                    updated_account_comms[i],
                ),
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_encs[i].core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);
    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    for i in 0..batch_size {
        proofs[i]
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_encs[i].core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comms[i],
                nullifiers[i],
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();
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
fn swap_settlement() {
    // Full reversible swap (hidden asset-ids): Alice<->Bob exchange two different assets via two legs, each with a
    // LegCreationProof (asset curve-tree membership) + ordinary affirm proofs that bump counters.
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;
    let (account_tree_params, asset_tree_params, _, account_comm_key, enc_gen) =
        setup_asset_and_account_params_new::<NUM_GENS>();

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        1,
        account_tree_params.odd_parameters.bp_gens(),
    );

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (sk_e, pk_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    let asset_tree_height = 4;
    let account_tree_height = 6;

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Both assets have same mediator
    let (sk_m, pk_m) = keygen_sig(&mut rng, account_comm_key.sk_gen());
    let keys_enc = vec![pk_e.0];
    let keys_med = vec![pk_m.0];
    let asset_data_1 = AssetData::new(
        asset_id_1,
        keys_enc.clone(),
        keys_med.clone(),
        &asset_comm_params,
    )
    .unwrap();
    let asset_data_2 = AssetData::new(
        asset_id_2,
        keys_enc.clone(),
        keys_med.clone(),
        &asset_comm_params,
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
    let (leg_1, leg_enc_1, leg_enc_rand_1) = setup_leg(
        &mut rng,
        pk_e.0,
        Some(pk_m.0),
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_2, leg_enc_2, leg_enc_rand_2) = setup_leg(
        &mut rng,
        pk_e.0,
        Some(pk_m.0),
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _, _) = new_account(&mut rng, asset_id_1, pk_s, pk_s_e, alice_id);
    alice_account_1.balance = 200;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _, _) = new_account(&mut rng, asset_id_2, pk_s, pk_s_e, alice_id);
    alice_account_2.balance = 50;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _, _) = new_account(&mut rng, asset_id_1, pk_r, pk_r_e, bob_id);
    bob_account_1.balance = 50;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _, _) = new_account(&mut rng, asset_id_2, pk_r, pk_r_e, bob_id);
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
    let (mut even_prover_settlement, mut odd_prover_settlement) = create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof_1 =
        LegCreationProof::new_with_given_prover::<_, PallasParams, VestaParams>(
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
            account_comm_key.sk_enc_gen(),
            enc_gen,
            &mut even_prover_settlement,
            &mut odd_prover_settlement,
        )
        .unwrap();

    let settlement_proof_2 =
        LegCreationProof::new_with_given_prover::<_, PallasParams, VestaParams>(
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
            account_comm_key.sk_enc_gen(),
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
        create_verifiers::<VestaParameters, PallasParameters>(
            LEG_TXN_EVEN_LABEL,
            LEG_TXN_ODD_LABEL,
        );

    settlement_proof_1
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_1.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
        create_verifiers::<VestaParameters, PallasParameters>(
            LEG_TXN_EVEN_LABEL,
            LEG_TXN_ODD_LABEL,
        );

    settlement_proof_1
        .verify_sigma_protocols_and_enforce_constraints(
            leg_enc_1.clone(),
            &asset_tree_root,
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

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
        sk_m.0,
        sk_e.0,
        index_in_asset_data,
        index_in_asset_data,
        accept,
        nonce,
        &leg_enc_1.mediators.as_ref().unwrap()[index_in_asset_data],
        account_comm_key.sk_gen(),
        &mut transcript,
    )
    .unwrap();

    let med_proof_2 = MediatorTxnProof::new_with_given_transcript(
        &mut rng,
        sk_m.0,
        sk_e.0,
        index_in_asset_data,
        index_in_asset_data,
        accept,
        nonce,
        &leg_enc_2.mediators.as_ref().unwrap()[index_in_asset_data],
        account_comm_key.sk_gen(),
        &mut transcript,
    )
    .unwrap();

    let mediator_proving_time = clock.elapsed();

    let clock = Instant::now();
    let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

    med_proof_1
        .verify_with_given_transcript(
            index_in_asset_data,
            accept,
            nonce,
            &leg_enc_1.mediators.as_ref().unwrap()[index_in_asset_data],
            account_comm_key.sk_gen(),
            &mut transcript,
        )
        .unwrap();

    med_proof_2
        .verify_with_given_transcript(
            index_in_asset_data,
            accept,
            nonce,
            &leg_enc_2.mediators.as_ref().unwrap()[index_in_asset_data],
            account_comm_key.sk_gen(),
            &mut transcript,
        )
        .unwrap();

    let mediator_verification_time = clock.elapsed();

    // Combined alice proofs for both legs (alice sends in leg1, receives in leg2)
    let clock = Instant::now();
    let (mut even_prover_alice, mut odd_prover_alice) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Alice proof for leg1 (sending asset1)
    let (alice_proof_leg1, alice_nullifier_leg1) =
        AffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc_1.core_and_eph_keys_for_sender();
                (c, e, amount_1)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_1.clone(),
                updated_alice_account_1.clone(),
                updated_alice_account_comm_1,
            ),
            alice_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    // Alice proof for leg2 (receiving asset2)
    let (alice_proof_leg2, alice_nullifier_leg2) =
        AffirmAsReceiverTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_2.clone(),
                updated_alice_account_2.clone(),
                updated_alice_account_comm_2,
            ),
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    let (mut even_prover_bob, mut odd_prover_bob) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Bob proof for leg1 (receiving asset1)
    let (bob_proof_leg1, bob_nullifier_leg1) =
        AffirmAsReceiverTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_1,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_1.clone(),
                updated_bob_account_1.clone(),
                updated_bob_account_comm_1,
            ),
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    // Bob proof for leg2 (sending asset2)
    let (bob_proof_leg2, bob_nullifier_leg2) =
        AffirmAsSenderTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_2.clone(),
                updated_bob_account_2.clone(),
                updated_bob_account_comm_2,
            ),
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

    let alice_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut bob_even_verifier, mut bob_odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

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
    let (mut even_prover_alice, mut odd_prover_alice) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (alice_counter_update_proof, alice_cu_nullifier) =
        SenderCounterUpdateTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc_1.core_and_eph_keys_for_sender();
                (c, e, amount_1)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                updated_alice_account_1.clone(),
                updated_alice_account_4.clone(),
                updated_alice_account_comm_4,
            ),
            alice_1_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    let (alice_claim_proof, alice_claim_nullifier) =
        ClaimReceivedTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                updated_alice_account_2.clone(),
                updated_alice_account_3.clone(),
                updated_alice_account_comm_3,
            ),
            alice_2_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    let (mut even_prover_bob, mut odd_prover_bob) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    let (bob_claim_proof, bob_claim_nullifier) =
        ClaimReceivedTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_1,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                updated_bob_account_1.clone(),
                updated_bob_account_3.clone(),
                updated_bob_account_comm_3,
            ),
            bob_1_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    let (bob_counter_update_proof, bob_cu_nullifier) =
        SenderCounterUpdateTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                updated_bob_account_2.clone(),
                updated_bob_account_4.clone(),
                updated_bob_account_comm_4,
            ),
            bob_2_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_4,
            alice_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_3,
            alice_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    // Verify Bob counter update proofs
    bob_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_3,
            bob_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_4,
            bob_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_4,
            alice_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    alice_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_3,
            alice_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

    let alice_counter_update_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut bob_even_verifier, mut bob_odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    // Verify Bob counter update proofs
    bob_claim_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_3,
            bob_claim_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    bob_counter_update_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_4,
            bob_cu_nullifier,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

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
        "Mediator affirmation proving time = {:?}, verification time = {:?}, proof size = {} bytes",
        mediator_proving_time, mediator_verification_time, mediator_proof_size
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
    // Both parties roll back a previously-affirmed 2-leg swap (hidden asset-ids): each account starts with counter=1
    // and the sender un-sends (restores balance) while the receiver just decrements its pending counter.
    let mut rng = rand::thread_rng();

    // Setup begins
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    // Setup keys for sender, receiver, and auditor
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    // Two different asset-ids for swap
    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let amount_1 = 100;
    let amount_2 = 200;

    // Create two legs for swap
    let (_, leg_enc_1, _) = setup_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_1,
        asset_id_1,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (_, leg_enc_2, _) = setup_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount_2,
        asset_id_2,
        pk_r_e.0,
        pk_s_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Alice has accounts for both assets
    let alice_id = PallasFr::rand(&mut rng);
    let (mut alice_account_1, _, _, _) = new_account(&mut rng, asset_id_1, pk_s, pk_s_e, alice_id);
    alice_account_1.balance = 500;
    alice_account_1.counter = 1;
    let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut alice_account_2, _, _, _) = new_account(&mut rng, asset_id_2, pk_s, pk_s_e, alice_id);
    alice_account_2.balance = 50;
    alice_account_2.counter = 1;
    let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

    // Bob has accounts for both assets
    let bob_id = PallasFr::rand(&mut rng);
    let (mut bob_account_1, _, _, _) = new_account(&mut rng, asset_id_1, pk_r, pk_r_e, bob_id);
    bob_account_1.balance = 500;
    bob_account_1.counter = 1;
    let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

    let (mut bob_account_2, _, _, _) = new_account(&mut rng, asset_id_2, pk_r, pk_r_e, bob_id);
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
        Some(6),
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
    let (mut even_prover_alice, mut odd_prover_alice) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Alice proof for leg1 (reverse sending asset1)
    let (alice_proof_leg1, alice_nullifier_leg1) =
        SenderReverseTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc_1.core_and_eph_keys_for_sender();
                (c, e, amount_1)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_1.clone(),
                updated_alice_account_1.clone(),
                updated_alice_account_comm_1,
            ),
            alice_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_alice,
            &mut odd_prover_alice,
        )
        .unwrap();

    // Alice proof for leg2 (reverse receiving asset2)
    let (alice_proof_leg2, alice_nullifier_leg2) =
        ReceiverCounterUpdateTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                alice_account_2.clone(),
                updated_alice_account_2.clone(),
                updated_alice_account_comm_2,
            ),
            alice_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    let (mut even_prover_bob, mut odd_prover_bob) = create_provers(
        TXN_EVEN_LABEL,
        TXN_ODD_LABEL,
        account_tree_params.even_parameters.pc_gens(),
        account_tree_params.odd_parameters.pc_gens(),
    );

    // Bob proof for leg1 (reverse receiving asset1)
    let (bob_proof_leg1, bob_nullifier_leg1) =
        ReceiverCounterUpdateTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                amount_1,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_1.clone(),
                updated_bob_account_1.clone(),
                updated_bob_account_comm_1,
            ),
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

    // Bob proof for leg2 (reverse sending asset2)
    let (bob_proof_leg2, bob_nullifier_leg2) =
        SenderReverseTxnProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                amount_2,
            ),
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                bob_account_2.clone(),
                updated_bob_account_2.clone(),
                updated_bob_account_comm_2,
            ),
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            None,
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            None,
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    alice_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            leg_enc_1.core_and_eph_keys_for_sender(),
            &account_tree_root,
            updated_alice_account_comm_1,
            alice_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut alice_even_verifier,
            &mut alice_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    alice_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_alice_account_comm_2,
            alice_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

    let alice_verification_time_rmc = clock.elapsed();

    let clock = Instant::now();

    let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

    let (mut bob_even_verifier, mut bob_odd_verifier) =
        create_verifiers::<PallasParameters, VestaParameters>(TXN_EVEN_LABEL, TXN_ODD_LABEL);

    bob_proof_leg1
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_1,
            bob_nullifier_leg1,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            &mut bob_even_verifier,
            &mut bob_odd_verifier,
            Some(&mut rmc_0),
        )
        .unwrap();

    bob_proof_leg2
        .enforce_constraints_and_verify_only_sigma_protocols(
            (
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ),
            &account_tree_root,
            updated_bob_account_comm_2,
            bob_nullifier_leg2,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

    let bob_verification_time_rmc = clock.elapsed();

    let alice_affirmation_proof_size = alice_even_bp.compressed_size()
        + alice_odd_bp.compressed_size()
        + alice_proof_leg1.compressed_size()
        + alice_proof_leg2.compressed_size();

    let bob_affirmation_proof_size = bob_even_bp.compressed_size()
        + bob_odd_bp.compressed_size()
        + bob_proof_leg1.compressed_size()
        + bob_proof_leg2.compressed_size();

    println!("For L={L}, height={}", account_tree.height());
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
fn multi_asset_settlement() {
    // 10-leg settlement spanning several asset-ids: one SettlementCreationProof for all legs, and each party's many
    // per-leg irreversible state transitions are batched into a single MultiAssetStateTransitionProof.
    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 4;
    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;

    let num_legs = 10;
    let asset_tree_height = 4;
    let account_tree_height = 6;

    let (
        asset_data_vec,
        asset_paths,
        asset_tree_root,
        legs,
        leg_encs,
        leg_enc_rands,
        alice_accounts,
        (sk_s, sk_s_e),
        bob_accounts,
        (sk_r, sk_r_e),
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
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
    let settlement_proof = SettlementCreationProof::new::<_, PallasParams, VestaParams>(
        &mut rng,
        legs,
        leg_encs.clone(),
        leg_enc_rands,
        asset_paths,
        asset_data_vec,
        &asset_tree_root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        account_comm_key.sk_enc_gen(),
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
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    alice_accounts[i].clone(),
                    updated_account,
                    updated_comm,
                ),
                nonce,
            );
        builder.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            amount,
        ));
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
    >::new::<_, PallasParams, VestaParams>(
        &mut rng,
        alice_builders,
        alice_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
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
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    bob_accounts[i].clone(),
                    updated_account,
                    updated_comm,
                ),
                nonce,
            );
        builder.add_irreversible_receive({
            let (c, e) = leg_encs[i].core_and_eph_keys_for_receiver();
            (c, e, amount)
        });
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
    >::new::<_, PallasParams, VestaParams>(
        &mut rng,
        bob_builders,
        bob_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
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
        alice_verifiers[i].add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
        ));
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
        bob_verifiers[i].add_irreversible_receive(leg_encs[i].core_and_eph_keys_for_receiver());
    }

    let (settlement_even, settlement_odd) = settlement_proof
        .verify_and_return_tuples(
            leg_encs.clone(),
            &asset_tree_root,
            vec![],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
            vec![],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
        verifier.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
        ));
        alice_verifiers.push(verifier);
    }

    let (alice_even, alice_odd) = alice_proof
        .verify_and_return_tuples(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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
        verifier.add_irreversible_receive(leg_encs[i].core_and_eph_keys_for_receiver());
        bob_verifiers.push(verifier);
    }

    let (bob_even, bob_odd) = bob_proof
        .verify_and_return_tuples(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

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

#[test]
fn multi_asset_combined_create_and_send() {
    // multi_asset_settlement but the SettlementCreationProof is folded with the SENDER's MultiAssetStateTransition
    // into one shared prover/aggregated proof; the receiver's multi-asset proof is built separately.
    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 4;
    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;

    let num_legs = 10;
    let asset_tree_height = 4;
    let account_tree_height = 6;

    let (
        asset_data_vec,
        asset_paths,
        asset_tree_root,
        legs,
        leg_encs,
        leg_enc_rands,
        alice_accounts,
        (sk_s, sk_s_e),
        bob_accounts,
        (sk_r, sk_r_e),
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
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

    let (mut even_prover, mut odd_prover) = create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof =
        SettlementCreationProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            legs,
            leg_encs.clone(),
            leg_enc_rands,
            asset_paths,
            asset_data_vec,
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    alice_accounts[i].clone(),
                    updated_account,
                    updated_comm,
                ),
                nonce,
            );
        builder.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            amount,
        ));
        alice_builders.push(builder);
    }

    let (alice_proof, alice_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover::<_, PallasParams, VestaParams>(
        &mut rng,
        alice_builders,
        alice_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
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
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    bob_accounts[i].clone(),
                    updated_account,
                    updated_comm,
                ),
                nonce,
            );
        builder.add_irreversible_receive({
            let (c, e) = leg_encs[i].core_and_eph_keys_for_receiver();
            (c, e, amount)
        });
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
    >::new::<_, PallasParams, VestaParams>(
        &mut rng,
        bob_builders,
        bob_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
    )
    .unwrap();
    let bob_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            vec![],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
        verifier.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
        ));
        alice_verifiers.push(verifier);
    }

    alice_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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
        verifier.add_irreversible_receive(leg_encs[i].core_and_eph_keys_for_receiver());
        bob_verifiers.push(verifier);
    }

    let (bob_even, bob_odd) = bob_proof
        .verify_and_return_tuples(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            vec![],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
        verifier.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
        ));
        alice_verifiers.push(verifier);
    }

    alice_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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
        verifier.add_irreversible_receive(leg_encs[i].core_and_eph_keys_for_receiver());
        bob_verifiers.push(verifier);
    }

    let (bob_even, bob_odd) = bob_proof
        .verify_and_return_tuples(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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
    verify_rmc(rmc_0, rmc_1).unwrap();

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

#[test]
fn multi_asset_combined_create_and_recv() {
    // Mirror of multi_asset_combined_create_and_send: folds SettlementCreationProof with the RECEIVER's
    // MultiAssetStateTransition into one shared proof; the sender's multi-asset proof is built separately.
    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;
    const ASSET_TREE_M: usize = 4;
    const ACCOUNT_TREE_M: usize = 4;

    let num_legs = 10;
    let asset_tree_height = 4;
    let account_tree_height = 6;

    let (
        asset_data_vec,
        asset_paths,
        asset_tree_root,
        legs,
        leg_encs,
        leg_enc_rands,
        alice_accounts,
        (sk_s, sk_s_e),
        bob_accounts,
        (sk_r, sk_r_e),
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
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

    let (mut even_prover, mut odd_prover) = create_provers(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
    );

    let settlement_proof =
        SettlementCreationProof::new_with_given_prover::<_, PallasParams, VestaParams>(
            &mut rng,
            legs,
            leg_encs.clone(),
            leg_enc_rands,
            asset_paths,
            asset_data_vec,
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    bob_accounts[i].clone(),
                    updated_account,
                    updated_comm,
                ),
                nonce,
            );
        builder.add_irreversible_receive({
            let (c, e) = leg_encs[i].core_and_eph_keys_for_receiver();
            (c, e, amount)
        });
        bob_builders.push(builder);
    }

    let (bob_proof, bob_nullifiers) = MultiAssetStateTransitionProof::<
        L,
        ACCOUNT_TREE_M,
        _,
        _,
        PallasParameters,
        VestaParameters,
    >::new_with_given_prover::<_, PallasParams, VestaParams>(
        &mut rng,
        bob_builders,
        bob_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
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
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    alice_accounts[i].clone(),
                    updated_account,
                    updated_comm,
                ),
                nonce,
            );
        builder.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            amount,
        ));
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
    >::new::<_, PallasParams, VestaParams>(
        &mut rng,
        alice_builders,
        alice_paths,
        &account_tree_root,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
    )
    .unwrap();
    let alice_proving_time = start.elapsed();

    let start = Instant::now();

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            vec![],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
        bob_verifiers[i].add_irreversible_receive(leg_encs[i].core_and_eph_keys_for_receiver());
    }

    bob_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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
        verifier.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
        ));
        alice_verifiers.push(verifier);
    }

    let (alice_even, alice_odd) = alice_proof
        .verify_and_return_tuples(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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

    let (mut even_verifier, mut odd_verifier) = create_verifiers::<VestaParameters, PallasParameters>(
        LEG_TXN_EVEN_LABEL,
        LEG_TXN_ODD_LABEL,
    );
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    settlement_proof
        .verify_sigma_protocols_and_enforce_constraints(
            leg_encs.clone(),
            &asset_tree_root,
            vec![],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            account_comm_key.sk_enc_gen(),
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
        bob_verifiers[i].add_irreversible_receive(leg_encs[i].core_and_eph_keys_for_receiver());
    }

    bob_proof
        .enforce_constraints_and_verify_only_sigma_protocols(
            bob_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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
        verifier.add_irreversible_send((
            leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
            leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
        ));
        alice_verifiers.push(verifier);
    }

    let (alice_even, alice_odd) = alice_proof
        .verify_and_return_tuples(
            alice_verifiers,
            &account_tree_root,
            &account_tree_params,
            account_comm_key.clone(),
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

    verify_rmc(rmc_0, rmc_1).unwrap();

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

#[test]
fn multi_asset_state_transition_different_confs() {
    // Runs the same multi-asset receive-affirmation proof under four (L, M) configs -- leaf width 64/128 and
    // batched-path width 2/4 at differing tree heights -- to check it holds across curve-tree parameter choices.
    fn check<const L: usize, const M: usize>(
        num_legs: usize,
        height: usize,
        account_tree_params: &SelRerandProofParametersNew<
            PallasParameters,
            VestaParameters,
            PallasParams,
            VestaParams,
        >,
        account_comm_key: impl AccountCommitmentKeyTrait<PallasA> + Clone,
        enc_gen: PallasA,
    ) {
        let mut rng = rand::thread_rng();

        let (
            ((sk_alice, pk_alice), (sk_alice_e, pk_alice_e)),
            ((_sk_bob, pk_bob), (_sk_bob_e, pk_bob_e)),
            (_, (_, pk_auditor_e)),
        ) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        // Create legs, all with same sender (Alice) and receiver (Bob) but different assets
        let mut leg_encs = Vec::with_capacity(num_legs);
        let amount = 100;

        for asset_id in 1..=num_legs as u32 {
            let (_, leg_enc, _) = setup_leg(
                &mut rng,
                pk_auditor_e.0,
                None,
                amount,
                asset_id,
                pk_bob_e.0,
                pk_alice_e.0,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            );
            leg_encs.push(leg_enc);
        }

        // Create Alice's accounts, one per asset
        let alice_id = PallasFr::rand(&mut rng);
        let mut alice_accounts = Vec::with_capacity(num_legs);
        let mut alice_account_comms = Vec::with_capacity(num_legs);

        for asset_id in 1..=num_legs as u32 {
            let (mut account, _, _, _) =
                new_account(&mut rng, asset_id, pk_alice, pk_alice_e, alice_id);
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
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_bob, pk_bob_e, bob_id);
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
                AccountTxnWitness::new(
                    sk_alice.0,
                    sk_alice_e.0,
                    alice_accounts[i].clone(),
                    updated_account,
                    updated_comm,
                ),
                nonce,
            );
            builder.add_receive_affirmation({
                let (c, e) = leg_encs[i].core_and_eph_keys_for_receiver();
                (c, e, amount)
            });
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
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                alice_builders,
                alice_paths,
                &account_tree_root,
                account_tree_params,
                account_comm_key.clone(),
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
            verifier.add_receive_affirmation(leg_encs[i].core_and_eph_keys_for_receiver());
            alice_verifiers.push(verifier);
        }

        let (alice_even, alice_odd) = alice_proof
            .verify_and_return_tuples(
                alice_verifiers,
                &account_tree_root,
                account_tree_params,
                account_comm_key.clone(),
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
            verifier.add_receive_affirmation(leg_encs[i].core_and_eph_keys_for_receiver());
            alice_verifiers.push(verifier);
        }

        let (alice_even, alice_odd) = alice_proof
            .verify_and_return_tuples(
                alice_verifiers,
                &account_tree_root,
                account_tree_params,
                account_comm_key.clone(),
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
        verify_rmc(rmc_0, rmc_1).unwrap();

        let verify_rmc_time = start.elapsed();

        println!(
            "Regular verify time = {:?} and with rmc time = {:?}",
            verify_time, verify_rmc_time
        );
    }

    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<{ 1 << 12 }>(b"test");

    check::<64, 2>(
        8,
        6,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
    );
    check::<64, 4>(
        8,
        6,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
    );
    check::<128, 2>(
        8,
        5,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
    );
    check::<128, 4>(
        8,
        5,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
    );
}

pub fn setup_leg<R: CryptoRngCore>(
    rng: &mut R,
    pk_e: PallasA,
    pk_m: Option<PallasA>,
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
    let conf = LegEncConfig::default();
    setup_leg_with_conf(
        rng,
        conf,
        pk_e,
        pk_m,
        amount,
        asset_id,
        pk_s_e,
        pk_r_e,
        enc_key_gen,
        enc_gen,
    )
}

pub fn setup_leg_with_conf<R: CryptoRngCore>(
    rng: &mut R,
    conf: LegEncConfig,
    pk_e: PallasA,
    pk_m: Option<PallasA>,
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
    let enc_keys = vec![pk_e];
    let med_keys = if pk_m.is_some() {
        vec![pk_m.unwrap()]
    } else {
        vec![]
    };
    let leg = Leg::new(pk_s_e, pk_r_e, amount, asset_id, enc_keys, med_keys, vec![]).unwrap();
    let (leg_enc, leg_enc_rand) = leg.encrypt(rng, conf, enc_key_gen, enc_gen).unwrap();
    (leg, leg_enc, leg_enc_rand)
}

/// Create a new tree and add the given account's commitment to the tree and return the tree
/// In future, allow to generate tree many given number of leaves and add the account commitment to a
/// random position in tree.
pub fn get_tree_with_account_comm<
    const L: usize,
    P: SelRerandParametersRef<PallasParameters, VestaParameters>,
>(
    account: &AccountState<PallasA>,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    account_tree_params: &P,
    tree_height: usize,
) -> Result<CurveTree<L, 1, PallasParameters, VestaParameters>> {
    let account_comm = account.commit(account_comm_key)?;

    Ok(get_tree_with_commitment(
        account_comm,
        account_tree_params,
        tree_height,
    ))
}

/// Create a new tree and add the given account commitment to the tree and return the tree
pub fn get_tree_with_commitment<
    const L: usize,
    P: SelRerandParametersRef<PallasParameters, VestaParameters>,
>(
    account_comm: AccountStateCommitment<PallasA>,
    account_tree_params: &P,
    tree_height: usize,
) -> CurveTree<L, 1, PallasParameters, VestaParameters> {
    let set = vec![account_comm.0];
    CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        account_tree_params,
        Some(tree_height),
    )
}

/// Create a batched tree with multiple account commitments
pub fn get_batched_tree_with_account_comms<
    const L: usize,
    const M: usize,
    P: SelRerandParametersRef<PallasParameters, VestaParameters>,
>(
    accounts: Vec<&AccountState<PallasA>>,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    account_tree_params: &P,
    tree_height: usize,
) -> Result<CurveTree<L, M, PallasParameters, VestaParameters>> {
    let account_comms: Vec<_> = accounts
        .iter()
        .map(|account| account.commit(account_comm_key.clone()).map(|c| c.0))
        .collect::<Result<Vec<_>>>()?;

    Ok(
        CurveTree::<L, M, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            account_tree_params,
            Some(tree_height),
        ),
    )
}

/// Setup parameters for new proof protocol
pub fn setup_gens_new<const NUM_GENS: usize>(
    label: &[u8],
) -> (
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    // Create public params with generator tables for new divisor-based proof protocol
    let account_tree_params = SelRerandProofParametersNew::<
        PallasParameters,
        VestaParameters,
        PallasParams,
        VestaParams,
    >::new(NUM_GENS as u32, NUM_GENS as u32)
    .unwrap();
    let account_comm_key = setup_comm_key(label);
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();
    (account_tree_params, account_comm_key, enc_gen)
}

/// Setup asset and account params for new proof protocol
pub fn setup_asset_and_account_params_new<const NUM_GENS: usize>() -> (
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    SelRerandProofParametersNew<VestaParameters, PallasParameters, VestaParams, PallasParams>,
    AssetCommitmentParams<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_tree_params = SelRerandProofParametersNew::<
        VestaParameters,
        PallasParameters,
        VestaParams,
        PallasParams,
    >::new(NUM_GENS as u32, NUM_GENS as u32)
    .unwrap();

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        0,
        account_tree_params.odd_parameters.bp_gens(),
    );

    (
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_gen,
    )
}

pub fn create_provers<'a, P0: SWCurveConfig + Copy + Clone, P1: SWCurveConfig + Copy + Clone>(
    label_even: &'static [u8],
    label_odd: &'static [u8],
    even_pc_gens: &'a PedersenGens<Affine<P0>>,
    odd_pc_gens: &'a PedersenGens<Affine<P1>>,
) -> (
    Prover<'a, MerlinTranscript, Affine<P0>>,
    Prover<'a, MerlinTranscript, Affine<P1>>,
) {
    let even_transcript = MerlinTranscript::new(label_even);
    let odd_transcript = MerlinTranscript::new(label_odd);
    let even_prover = Prover::new(even_pc_gens, even_transcript);
    let odd_prover = Prover::new(odd_pc_gens, odd_transcript);
    (even_prover, odd_prover)
}

pub fn create_verifiers<P0: SWCurveConfig + Copy + Clone, P1: SWCurveConfig + Copy + Clone>(
    label_even: &'static [u8],
    label_odd: &'static [u8],
) -> (
    Verifier<MerlinTranscript, Affine<P0>>,
    Verifier<MerlinTranscript, Affine<P1>>,
) {
    let even_transcript = MerlinTranscript::new(label_even);
    let odd_transcript = MerlinTranscript::new(label_odd);
    let even_verifier = Verifier::new(even_transcript);
    let odd_verifier = Verifier::new(odd_transcript);
    (even_verifier, odd_verifier)
}

pub fn setup_single_leg_settlement_common<
    const L: usize,
    AccountTreeParams: SelRerandParametersRef<PallasParameters, VestaParameters>,
    AssetTreeParams: SelRerandParametersRef<VestaParameters, PallasParameters>,
>(
    asset_tree_height: u64,
    account_tree_height: u64,
    account_tree_params: AccountTreeParams,
    asset_tree_params: AssetTreeParams,
    asset_comm_params: AssetCommitmentParams<PallasParameters, VestaParameters>,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    enc_gen: PallasA,
) -> (
    AssetData<PallasFr, VestaFr, PallasParameters, VestaParameters>,
    CurveTreeWitnessPath<L, VestaParameters, PallasParameters>,
    Root<L, 1, VestaParameters, PallasParameters>,
    Leg<PallasA>,
    LegEncryption<PallasA>,
    LegEncryptionRandomness<PallasFr>,
    AccountState<PallasA>,
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    AccountState<PallasA>,
    AccountStateCommitment<PallasA>,
    AccountStateCommitment<PallasA>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
    AccountTreeParams,
    AssetTreeParams,
    AssetCommitmentParams<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    let mut rng = rand::thread_rng();

    // All parties generate their keys
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    let asset_id = 1;
    let amount = 50;

    // Create asset data
    let keys = vec![pk_a_e.0];
    let asset_data = AssetData::new(asset_id, keys.clone(), vec![], &asset_comm_params).unwrap();

    // Create asset tree with the asset commitment
    let set = vec![asset_data.commitment];
    let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
        &set,
        &asset_tree_params,
        Some(asset_tree_height as usize),
    );

    // Get asset tree path
    let asset_path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let asset_tree_root = asset_tree.root_node();

    // Create a single leg
    let (leg, leg_enc, leg_enc_rand) = setup_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Create sender account
    let sender_id = PallasFr::rand(&mut rng);
    let (mut sender_account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, sender_id);
    sender_account.balance = 200; // Ensure sufficient balance
    let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

    // Create receiver account
    let receiver_id = PallasFr::rand(&mut rng);
    let (mut receiver_account, _, _, _) =
        new_account(&mut rng, asset_id, pk_r, pk_r_e, receiver_id);
    receiver_account.balance = 150; // Some initial balance
    let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();

    // Create the account tree with both accounts
    let account_comms = vec![sender_account_comm.0, receiver_account_comm.0];
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &account_comms,
        &account_tree_params,
        Some(account_tree_height as usize),
    );

    let account_tree_root = account_tree.root_node();

    // Prepare updated account states
    let updated_sender_account = sender_account
        .get_state_for_irreversible_send(amount)
        .unwrap();
    let updated_sender_account_comm = updated_sender_account
        .commit(account_comm_key.clone())
        .unwrap();
    let sender_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_receiver_account = receiver_account
        .get_state_for_irreversible_receive(amount)
        .unwrap();
    let updated_receiver_account_comm = updated_receiver_account
        .commit(account_comm_key.clone())
        .unwrap();
    let receiver_path = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    (
        asset_data,
        asset_path,
        asset_tree_root,
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
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
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    AccountState<PallasA>,
    AccountStateCommitment<PallasA>,
    AccountStateCommitment<PallasA>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    SelRerandProofParametersNew<VestaParameters, PallasParameters, VestaParams, PallasParams>,
    AssetCommitmentParams<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    let (account_tree_params, account_comm_key, enc_gen) =
        setup_gens_new::<NUM_GENS>(b"test_settlement");

    // Create asset tree params (swapped curves for asset tree)
    let asset_tree_params = SelRerandProofParametersNew::<
        VestaParameters,
        PallasParameters,
        VestaParams,
        PallasParams,
    >::new(NUM_GENS as u32, NUM_GENS as u32)
    .unwrap();

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        0,
        &account_tree_params.odd_parameters.bp_gens(),
    );

    setup_single_leg_settlement_common(
        asset_tree_height,
        account_tree_height,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_gen,
    )
}

pub fn setup_multi_asset_settlement<
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
    (SigKey<PallasA>, DecKey<PallasA>),
    Vec<AccountState<PallasA>>,
    (SigKey<PallasA>, DecKey<PallasA>),
    Vec<CurveTreeWitnessMultiPath<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>>,
    Vec<CurveTreeWitnessMultiPath<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>>,
    Root<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>,
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    SelRerandProofParametersNew<VestaParameters, PallasParameters, VestaParams, PallasParams>,
    AssetCommitmentParams<PallasParameters, VestaParameters>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, asset_tree_params, asset_comm_params, account_comm_key, enc_gen) =
        setup_asset_and_account_params_new::<NUM_GENS>();

    let (
        ((sk_alice, pk_alice), (sk_alice_e, pk_alice_e)),
        ((sk_bob, pk_bob), (sk_bob_e, pk_bob_e)),
        (_, (_, pk_auditor_e)),
    ) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let keys = vec![pk_auditor_e.0];
    let mut asset_data_vec = Vec::with_capacity(num_legs);
    let mut asset_commitments = Vec::with_capacity(num_legs);

    for asset_id in 1..=num_legs as u32 {
        let asset_data =
            AssetData::new(asset_id, keys.clone(), vec![], &asset_comm_params).unwrap();
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
        let (leg, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_auditor_e.0,
            None,
            amount,
            asset_id,
            pk_alice_e.0,
            pk_bob_e.0,
            account_comm_key.sk_enc_gen(),
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
        let (mut account, _, _, _) =
            new_account(&mut rng, asset_id, pk_alice, pk_alice_e, alice_id);
        account.balance = 500;
        let comm = account.commit(account_comm_key.clone()).unwrap();
        alice_account_comms.push(comm.0);
        alice_accounts.push(account);
    }

    let bob_id = PallasFr::rand(&mut rng);
    let mut bob_accounts = Vec::with_capacity(num_legs);
    let mut bob_account_comms = Vec::with_capacity(num_legs);

    for asset_id in 1..=num_legs as u32 {
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_bob, pk_bob_e, bob_id);
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
        (sk_alice, sk_alice_e),
        bob_accounts,
        (sk_bob, sk_bob_e),
        alice_paths,
        bob_paths,
        account_tree_root,
        account_tree_params,
        asset_tree_params,
        asset_comm_params,
        account_comm_key,
        enc_gen,
    )
}

/// Setup helper for public asset leg (revealed asset_id)
pub fn setup_public_asset_leg<R: CryptoRngCore>(
    rng: &mut R,
    pk_e: PallasA,
    pk_m: Option<PallasA>,
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
    let conf = LegEncConfig {
        parties_see_each_other: true,
        reveal_asset_id: true,
    };
    let enc_keys = vec![pk_e];
    let med_keys = if pk_m.is_some() {
        vec![pk_m.unwrap()]
    } else {
        vec![]
    };
    let leg = Leg::new(pk_s_e, pk_r_e, amount, asset_id, enc_keys, med_keys, vec![]).unwrap();
    let (leg_enc, leg_enc_rand) = leg.encrypt(rng, conf, enc_key_gen, enc_gen).unwrap();
    (leg, leg_enc, leg_enc_rand)
}

/// Setup for single leg settlement with revealed asset_id (no asset tree needed)
pub fn setup_single_leg_settlement_public_asset_common<
    const L: usize,
    AccountTreeParams: SelRerandParametersRef<PallasParameters, VestaParameters>,
>(
    account_tree_height: u64,
    account_tree_params: AccountTreeParams,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    enc_gen: PallasA,
) -> (
    Leg<PallasA>,
    LegEncryption<PallasA>,
    LegEncryptionRandomness<PallasFr>,
    AccountState<PallasA>,
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    AccountState<PallasA>,
    AccountStateCommitment<PallasA>,
    AccountStateCommitment<PallasA>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
    AccountTreeParams,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    let mut rng = rand::thread_rng();

    // All parties generate their keys
    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

    let asset_id = 1;
    let amount = 50;

    // Create a single leg with revealed asset_id
    let (leg, leg_enc, leg_enc_rand) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    // Create sender account
    let sender_id = PallasFr::rand(&mut rng);
    let (mut sender_account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, sender_id);
    sender_account.balance = 200; // Ensure sufficient balance
    let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

    // Create receiver account
    let receiver_id = PallasFr::rand(&mut rng);
    let (mut receiver_account, _, _, _) =
        new_account(&mut rng, asset_id, pk_r, pk_r_e, receiver_id);
    receiver_account.balance = 150; // Some initial balance
    let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();

    // Create the account tree with both accounts
    let account_comms = vec![sender_account_comm.0, receiver_account_comm.0];
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &account_comms,
        &account_tree_params,
        Some(account_tree_height as usize),
    );

    let account_tree_root = account_tree.root_node();

    // Prepare updated account states
    let updated_sender_account = sender_account
        .get_state_for_irreversible_send(amount)
        .unwrap();
    let updated_sender_account_comm = updated_sender_account
        .commit(account_comm_key.clone())
        .unwrap();
    let sender_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

    let updated_receiver_account = receiver_account
        .get_state_for_irreversible_receive(amount)
        .unwrap();
    let updated_receiver_account_comm = updated_receiver_account
        .commit(account_comm_key.clone())
        .unwrap();
    let receiver_path = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

    (
        leg,
        leg_enc,
        leg_enc_rand,
        sender_account,
        (sk_s, sk_s_e),
        receiver_account,
        (sk_r, sk_r_e),
        updated_sender_account,
        updated_receiver_account,
        updated_sender_account_comm,
        updated_receiver_account_comm,
        sender_path,
        receiver_path,
        account_tree_root,
        account_tree_params,
        account_comm_key,
        enc_gen,
    )
}

pub fn setup_single_leg_settlement_public_asset<const NUM_GENS: usize, const L: usize>(
    account_tree_height: u64,
) -> (
    Leg<PallasA>,
    LegEncryption<PallasA>,
    LegEncryptionRandomness<PallasFr>,
    AccountState<PallasA>,
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    (SigKey<PallasA>, DecKey<PallasA>),
    AccountState<PallasA>,
    AccountState<PallasA>,
    AccountStateCommitment<PallasA>,
    AccountStateCommitment<PallasA>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    let (account_tree_params, account_comm_key, enc_gen) =
        setup_gens_new::<NUM_GENS>(b"test_public_asset_settlement");

    setup_single_leg_settlement_public_asset_common(
        account_tree_height,
        account_tree_params,
        account_comm_key,
        enc_gen,
    )
}

fn setup_single_leg_test<const L: usize, R: CryptoRngCore>(
    rng: &mut R,
    reveal_asset_id: bool,
    pk_a_e: PallasA,
    pk_s_e: PallasA,
    pk_r_e: PallasA,
    amount: Balance,
    asset_id: AssetId,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    enc_gen: PallasA,
    updated_account_comm: AccountStateCommitment<PallasA>,
    account_tree: &CurveTree<L, 1, PallasParameters, VestaParameters>,
) -> (
    LegEncryption<PallasA>,
    AccountStateCommitment<PallasA>,
    CurveTreeWitnessPath<L, PallasParameters, VestaParameters>,
    Root<L, 1, PallasParameters, VestaParameters>,
) {
    let conf = LegEncConfig {
        parties_see_each_other: true,
        reveal_asset_id,
    };
    let (_, leg_enc, _) = setup_leg_with_conf(
        rng,
        conf,
        pk_a_e,
        None,
        amount,
        asset_id,
        pk_s_e,
        pk_r_e,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();
    (leg_enc, updated_account_comm, path, root)
}

/// Extracts the Fiat-Shamir challenge and protocol data from the prover state.
/// Returns `(challenge_h, re_randomized_leaf, auth_rerandomization, auth_rand_new_comm)`.
macro_rules! extract_prover_challenge_and_data {
    ($even_prover:expr, $protocol:expr) => {{
        let challenge_h = $even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let re_randomized_leaf = $protocol.rerandomized_leaf();
        let auth_rerandomization = $protocol.auth_rerandomization();
        let auth_rand_new_comm = $protocol.auth_rand_new_comm();
        (
            challenge_h,
            re_randomized_leaf,
            auth_rerandomization,
            auth_rand_new_comm,
        )
    }};
}

/// Runs the verifier side of a split proof (challenge contribution, auth-proof
/// verification, and `verify_and_return_tuples`) and returns the
/// `(even_tuple, odd_tuple)` pair for the caller to verify or batch.
///
/// Call-site example:
/// ```ignore
/// let (even_tuple, odd_tuple) = check_split_proof!(
///     proof: split_proof,
///     party: Sender,
///     has_balance_decreased: Some(true),
///     updated_account_comm: updated_account_comm,
///     nullifier: nullifier,
///     root: &root,
///     nonce: nonce,
///     account_tree_params: &account_tree_params,
///     account_comm_key: &account_comm_key,
///     enc_gen: enc_gen,
///     leg_enc_core: &leg_enc_core,
///     eph_pk: &eph_pk,
///     b_blinding: b_blinding,
///     rng: &mut rng,
/// );
/// ```
/// Handles the prover side of a split proof: generates random blinding scalars,
/// calls `init`, extracts the Fiat-Shamir challenge via
/// `extract_prover_challenge_and_data!`, builds the `AuthProofAffirmation`,
/// calls `gen_proof`, and assembles the final proof.
///
/// Two arms:
/// - `with_amount;` — for protocols whose `init` takes `amount` and `k_1`
///   (`gen_proof` returns `(host_data, balance)`; assemble takes all three).
/// - `no_amount;`  — for protocols whose `init` takes only `k_asset_id`
///   (`gen_proof` returns `host_data`; assemble takes two args).
///
/// Returns `(split_proof, nullifier, host_proof_time)`.
macro_rules! gen_split_proof {
    (
        with_amount;
        Protocol: $proto_ty:ty,
        Proof: $proof_ty:ident,
        party: $party:ident,
        has_balance_changed: $hbc:expr,
        rng: $rng:expr,
        amount: $amount:expr,
        leg_enc_core: $lec:expr,
        eph_pk: $eph_pk:expr,
        old_account: $old:expr,
        updated_account: $new:expr,
        updated_account_comm: $uac:expr,
        path: $path:expr,
        root: $root:expr,
        nonce: $nonce:expr,
        account_tree_params: $atp:expr,
        account_comm_key: $ack:expr,
        enc_gen: $eg:expr,
        sk_scalar: $sk:expr,
        sk_e_scalar: $ske:expr,
        b_blinding: $bb:expr,
        reveal_asset_id: $rai:expr $(,)?
    ) => {{
        let k_1 = PallasFr::rand($rng);
        let k_asset_id = if !$rai {
            Some(PallasFr::rand($rng))
        } else {
            None
        };
        let clock = Instant::now();
        let (protocol, mut even_prover, odd_prover, nullifier) =
            <$proto_ty>::init::<_, PallasParams, VestaParams>(
                $rng,
                ($lec.clone(), $eph_pk.clone(), $amount),
                &$old,
                &$new,
                $uac,
                $path,
                $root,
                $nonce,
                $atp,
                $ack.clone(),
                $eg,
                k_1,
                k_asset_id,
            )
            .unwrap();
        let (challenge_h, re_randomized_leaf, auth_rerandomization, auth_rand_new_comm) =
            extract_prover_challenge_and_data!(even_prover, protocol);
        let auth_proof = AuthProofAffirmation::new(
            $rng,
            $sk,
            $ske,
            auth_rerandomization,
            auth_rand_new_comm,
            vec![k_1],
            if !$rai {
                vec![k_asset_id.unwrap()]
            } else {
                vec![]
            },
            vec![LegProverConfig {
                encryption: $lec.clone(),
                party_eph_pk: PartyEphemeralPublicKey::$party($eph_pk.clone()),
                amount: $amount,
                has_balance_changed: $hbc,
            }],
            &re_randomized_leaf,
            &$uac.0,
            nullifier,
            $nonce,
            $ack.sk_gen(),
            $ack.sk_enc_gen(),
            $bb,
            $eg,
        )
        .unwrap();
        let (host, balance) = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h,
                even_prover,
                odd_prover,
                $atp,
                $rng,
            )
            .unwrap();
        let host_proof_time = clock.elapsed();
        let split_proof = $proof_ty::assemble(host, balance, auth_proof);
        (split_proof, nullifier, host_proof_time)
    }};
    (
        no_amount;
        Protocol: $proto_ty:ty,
        Proof: $proof_ty:ident,
        party: $party:ident,
        has_balance_changed: $hbc:expr,
        rng: $rng:expr,
        amount: $amount:expr,
        leg_enc_core: $lec:expr,
        eph_pk: $eph_pk:expr,
        old_account: $old:expr,
        updated_account: $new:expr,
        updated_account_comm: $uac:expr,
        path: $path:expr,
        root: $root:expr,
        nonce: $nonce:expr,
        account_tree_params: $atp:expr,
        account_comm_key: $ack:expr,
        enc_gen: $eg:expr,
        sk_scalar: $sk:expr,
        sk_e_scalar: $ske:expr,
        b_blinding: $bb:expr,
        reveal_asset_id: $rai:expr $(,)?
    ) => {{
        // ct_amount is needed when the leg reveals its asset-id (even with no balance change)
        let k_1 = PallasFr::rand($rng);
        let k_asset_id = if !$rai {
            Some(PallasFr::rand($rng))
        } else {
            None
        };
        let clock = Instant::now();
        let (protocol, mut even_prover, odd_prover, nullifier) =
            <$proto_ty>::init::<_, PallasParams, VestaParams>(
                $rng,
                ($lec.clone(), $eph_pk.clone(), $amount),
                &$old,
                &$new,
                $uac,
                $path,
                $root,
                $nonce,
                $atp,
                $ack.clone(),
                $eg,
                k_asset_id,
                k_1,
            )
            .unwrap();
        let (challenge_h, re_randomized_leaf, auth_rerandomization, auth_rand_new_comm) =
            extract_prover_challenge_and_data!(even_prover, protocol);
        let auth_proof = AuthProofAffirmation::new(
            $rng,
            $sk,
            $ske,
            auth_rerandomization,
            auth_rand_new_comm,
            if $rai { vec![k_1] } else { vec![] },
            if !$rai {
                vec![k_asset_id.unwrap()]
            } else {
                vec![]
            },
            vec![LegProverConfig {
                encryption: $lec.clone(),
                party_eph_pk: PartyEphemeralPublicKey::$party($eph_pk.clone()),
                amount: $amount,
                has_balance_changed: $hbc,
            }],
            &re_randomized_leaf,
            &$uac.0,
            nullifier,
            $nonce,
            $ack.sk_gen(),
            $ack.sk_enc_gen(),
            $bb,
            $eg,
        )
        .unwrap();
        let host_data = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h,
                even_prover,
                odd_prover,
                $atp,
                $rng,
            )
            .unwrap();
        let host_proof_time = clock.elapsed();
        let split_proof = $proof_ty::assemble(host_data, auth_proof);
        (split_proof, nullifier, host_proof_time)
    }};
    // Sequential flow (with_amount): ledger_nonce = challenge_h || nonce; auth_proof hashed into transcript
    (
        sequential; with_amount;
        Protocol: $proto_ty:ty,
        Proof: $proof_ty:ident,
        party: $party:ident,
        has_balance_changed: $hbc:expr,
        rng: $rng:expr,
        amount: $amount:expr,
        leg_enc_core: $lec:expr,
        eph_pk: $eph_pk:expr,
        old_account: $old:expr,
        updated_account: $new:expr,
        updated_account_comm: $uac:expr,
        path: $path:expr,
        root: $root:expr,
        nonce: $nonce:expr,
        account_tree_params: $atp:expr,
        account_comm_key: $ack:expr,
        enc_gen: $eg:expr,
        sk_scalar: $sk:expr,
        sk_e_scalar: $ske:expr,
        b_blinding: $bb:expr,
        reveal_asset_id: $rai:expr $(,)?
    ) => {{
        let k_1 = PallasFr::rand($rng);
        let k_asset_id = if !$rai {
            Some(PallasFr::rand($rng))
        } else {
            None
        };
        let clock = Instant::now();
        let (protocol, mut even_prover, odd_prover, nullifier) =
            <$proto_ty>::init::<_, PallasParams, VestaParams>(
                $rng,
                ($lec.clone(), $eph_pk.clone(), $amount),
                &$old,
                &$new,
                $uac,
                $path,
                $root,
                $nonce,
                $atp,
                $ack.clone(),
                $eg,
                k_1,
                k_asset_id,
            )
            .unwrap();
        let (challenge_h, re_randomized_leaf, auth_rerandomization, auth_rand_new_comm) =
            extract_prover_challenge_and_data!(even_prover, protocol);
        // Sequential: ledger_nonce = challenge_h_bytes || nonce
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain($nonce.iter())
            .copied()
            .collect();
        let auth_proof = AuthProofAffirmation::new(
            $rng,
            $sk,
            $ske,
            auth_rerandomization,
            auth_rand_new_comm,
            vec![k_1],
            if !$rai {
                vec![k_asset_id.unwrap()]
            } else {
                vec![]
            },
            vec![LegProverConfig {
                encryption: $lec.clone(),
                party_eph_pk: PartyEphemeralPublicKey::$party($eph_pk.clone()),
                amount: $amount,
                has_balance_changed: $hbc,
            }],
            &re_randomized_leaf,
            &$uac.0,
            nullifier,
            &ledger_nonce,
            $ack.sk_gen(),
            $ack.sk_enc_gen(),
            $bb,
            $eg,
        )
        .unwrap();
        // Hash auth_proof into transcript to derive updated challenge
        let mut auth_proof_bytes = Vec::new();
        auth_proof
            .serialize_compressed(&mut auth_proof_bytes)
            .unwrap();
        even_prover
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes);
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let (host_data, balance) = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_final,
                even_prover,
                odd_prover,
                $atp,
                $rng,
            )
            .unwrap();
        let host_proof_time = clock.elapsed();
        let split_proof = $proof_ty::assemble(host_data, balance, auth_proof);
        (split_proof, nullifier, host_proof_time)
    }};
    // Sequential flow (no_amount): ledger_nonce = challenge_h || nonce; auth_proof hashed into transcript
    (
        sequential; no_amount;
        Protocol: $proto_ty:ty,
        Proof: $proof_ty:ident,
        party: $party:ident,
        has_balance_changed: $hbc:expr,
        rng: $rng:expr,
        amount: $amount:expr,
        leg_enc_core: $lec:expr,
        eph_pk: $eph_pk:expr,
        old_account: $old:expr,
        updated_account: $new:expr,
        updated_account_comm: $uac:expr,
        path: $path:expr,
        root: $root:expr,
        nonce: $nonce:expr,
        account_tree_params: $atp:expr,
        account_comm_key: $ack:expr,
        enc_gen: $eg:expr,
        sk_scalar: $sk:expr,
        sk_e_scalar: $ske:expr,
        b_blinding: $bb:expr,
        reveal_asset_id: $rai:expr $(,)?
    ) => {{
        let k_1 = PallasFr::rand($rng);
        let k_asset_id = if !$rai {
            Some(PallasFr::rand($rng))
        } else {
            None
        };
        let clock = Instant::now();
        let (protocol, mut even_prover, odd_prover, nullifier) =
            <$proto_ty>::init::<_, PallasParams, VestaParams>(
                $rng,
                ($lec.clone(), $eph_pk.clone(), $amount),
                &$old,
                &$new,
                $uac,
                $path,
                $root,
                $nonce,
                $atp,
                $ack.clone(),
                $eg,
                k_asset_id,
                k_1,
            )
            .unwrap();
        let (challenge_h, re_randomized_leaf, auth_rerandomization, auth_rand_new_comm) =
            extract_prover_challenge_and_data!(even_prover, protocol);
        // Sequential: ledger_nonce = challenge_h_bytes || nonce
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain($nonce.iter())
            .copied()
            .collect();
        let auth_proof = AuthProofAffirmation::new(
            $rng,
            $sk,
            $ske,
            auth_rerandomization,
            auth_rand_new_comm,
            if $rai { vec![k_1] } else { vec![] },
            if !$rai {
                vec![k_asset_id.unwrap()]
            } else {
                vec![]
            },
            vec![LegProverConfig {
                encryption: $lec.clone(),
                party_eph_pk: PartyEphemeralPublicKey::$party($eph_pk.clone()),
                amount: $amount,
                has_balance_changed: $hbc,
            }],
            &re_randomized_leaf,
            &$uac.0,
            nullifier,
            &ledger_nonce,
            $ack.sk_gen(),
            $ack.sk_enc_gen(),
            $bb,
            $eg,
        )
        .unwrap();
        // Hash auth_proof into transcript to derive updated challenge
        let mut auth_proof_bytes = Vec::new();
        auth_proof
            .serialize_compressed(&mut auth_proof_bytes)
            .unwrap();
        even_prover
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes);
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let host_data = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_final,
                even_prover,
                odd_prover,
                $atp,
                $rng,
            )
            .unwrap();
        let host_proof_time = clock.elapsed();
        let split_proof = $proof_ty::assemble(host_data, auth_proof);
        (split_proof, nullifier, host_proof_time)
    }};
}

macro_rules! verify_split_proof {
    (
        proof: $proof:expr,
        party: $party:ident,
        has_balance_decreased: $hbd:expr,
        updated_account_comm: $uac:expr,
        nullifier: $nullifier:expr,
        root: $root:expr,
        nonce: $nonce:expr,
        account_tree_params: $atp:expr,
        account_comm_key: $ack:expr,
        enc_gen: $eg:expr,
        leg_enc_core: $lec:expr,
        eph_pk: $eph_pk:expr,
        b_blinding: $bb:expr,
        rng: $rng:expr $(,)?
    ) => {{
        let mut verifier = $proof
            .challenge_contribution::<PallasParams, VestaParams>(
                $uac, $nullifier, $root, $nonce, $atp, $ack, $eg, $lec, $eph_pk,
            )
            .unwrap();
        let challenge_h_v = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let re_randomized_leaf_v = $proof
            .common
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf()
            .unwrap();
        $proof
            .common
            .auth_proof
            .verify(
                vec![LegVerifierConfig {
                    encryption: $lec.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::$party($eph_pk.clone()),
                    has_balance_decreased: $hbd,
                    has_counter_decreased: None,
                }],
                &re_randomized_leaf_v,
                &$uac.0,
                $nullifier,
                $nonce,
                $ack.sk_gen(),
                $ack.sk_enc_gen(),
                $bb,
                $eg,
                None,
            )
            .unwrap();
        $proof
            .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                verifier,
                &challenge_h_v,
                $uac,
                $nullifier,
                $atp,
                $ack,
                $eg,
                $rng,
                None,
            )
            .unwrap()
    }};
    // Sequential flow: ledger_nonce_v = challenge_h_v || nonce; auth_proof hashed into transcript
    (
        sequential;
        proof: $proof:expr,
        party: $party:ident,
        has_balance_decreased: $hbd:expr,
        updated_account_comm: $uac:expr,
        nullifier: $nullifier:expr,
        root: $root:expr,
        nonce: $nonce:expr,
        account_tree_params: $atp:expr,
        account_comm_key: $ack:expr,
        enc_gen: $eg:expr,
        leg_enc_core: $lec:expr,
        eph_pk: $eph_pk:expr,
        b_blinding: $bb:expr,
        rng: $rng:expr $(,)?
    ) => {{
        let mut verifier = $proof
            .challenge_contribution::<PallasParams, VestaParams>(
                $uac, $nullifier, $root, $nonce, $atp, $ack, $eg, $lec, $eph_pk,
            )
            .unwrap();
        let challenge_h_v = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        // Sequential: reconstruct ledger_nonce_v = challenge_h_v_bytes || nonce
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain($nonce.iter())
            .copied()
            .collect();
        let re_randomized_leaf_v = $proof
            .common
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf()
            .unwrap();
        $proof
            .common
            .auth_proof
            .verify(
                vec![LegVerifierConfig {
                    encryption: $lec.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::$party($eph_pk.clone()),
                    has_balance_decreased: $hbd,
                    has_counter_decreased: None,
                }],
                &re_randomized_leaf_v,
                &$uac.0,
                $nullifier,
                &ledger_nonce_v,
                $ack.sk_gen(),
                $ack.sk_enc_gen(),
                $bb,
                $eg,
                None,
            )
            .unwrap();
        // Hash auth_proof into verifier transcript to derive updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        $proof
            .common
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        $proof
            .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                verifier,
                &challenge_h_final_v,
                $uac,
                $nullifier,
                $atp,
                $ack,
                $eg,
                $rng,
                None,
            )
            .unwrap()
    }};
}

#[test]
fn send_txn_split_proof() {
    // Sender's send proof produced jointly by a host (knows witnesses, not the secret key) and a secure device
    // (holds sk); exercises both the parallel (W2) and sequential (W3) combine flows, hidden & revealed asset-id.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_s_scalar = sk_s.0;
    let sk_s_e_scalar = sk_s_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();
        let (split_proof, nullifier, host_proof_time) = gen_split_proof!(
            with_amount;
            Protocol: AffirmAsSenderSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: AffirmAsSenderSplitProof,
            party: Sender,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        println!(
            "reveal_asset_id={}, host proof generation time = {:?}",
            reveal_asset_id, host_proof_time
        );
        println!("split proof size = {}", split_proof.compressed_size());

        let clock = Instant::now();
        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Sender,
            has_balance_decreased: Some(true),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();
        let verifier_time = clock.elapsed();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; with_amount;
            Protocol: AffirmAsSenderSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: AffirmAsSenderSplitProof,
            party: Sender,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let clock = Instant::now();
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Sender,
            has_balance_decreased: Some(true),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
        let verifier_time_seq = clock.elapsed();

        println!(
            "total prover time = {:?}, total verifier time (parallel W2) = {:?}, verifier time (sequential W3) = {:?}",
            host_proof_time, verifier_time, verifier_time_seq
        );
    };

    // asset-id hidden
    test_with_config(false);

    // asset-id revealed
    test_with_config(true);
}

#[test]
fn receive_txn_split_proof() {
    // Receiver's receive affirmation built jointly by host + secure device (holds sk); covers both parallel (W2)
    // and sequential (W3) combine flows and hidden/revealed asset-id.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_r_scalar = sk_r.0;
    let sk_r_e_scalar = sk_r_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_receive();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();
        let (split_proof, nullifier, host_proof_time) = gen_split_proof!(
            no_amount;
            Protocol: AffirmAsReceiverSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: AffirmAsReceiverSplitProof,
            party: Receiver,
            has_balance_changed: false,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        println!(
            "reveal_asset_id={}, host proof generation time = {:?}",
            reveal_asset_id, host_proof_time
        );
        println!("split proof size = {}", split_proof.compressed_size());

        let clock = Instant::now();
        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Receiver,
            has_balance_decreased: None,
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();
        let verifier_time = clock.elapsed();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; no_amount;
            Protocol: AffirmAsReceiverSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: AffirmAsReceiverSplitProof,
            party: Receiver,
            has_balance_changed: false,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let clock = Instant::now();
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Receiver,
            has_balance_decreased: None,
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
        let verifier_time_seq = clock.elapsed();

        println!(
            "total prover time = {:?}, total verifier time (parallel W2) = {:?}, verifier time (sequential W3) = {:?}",
            host_proof_time, verifier_time, verifier_time_seq
        );
    };

    // asset-id hidden
    test_with_config(false);

    // asset-id revealed
    test_with_config(true);
}

#[test]
fn claim_received_funds_split_proof() {
    // Receiver's claim (folds an affirmed amount into spendable balance, decrements counter) built jointly by
    // host + secure device (holds sk); covers both parallel (W2) and sequential (W3) flows and both asset-id modes.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_r_scalar = sk_r.0;
    let sk_r_e_scalar = sk_r_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    account.balance = 200;
    account.counter += 1;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_claiming_received(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();
        let (split_proof, nullifier, _host_proof_time) = gen_split_proof!(
            with_amount;
            Protocol: ClaimReceivedSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: ClaimReceivedSplitProof,
            party: Receiver,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Receiver,
            has_balance_decreased: Some(false),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; with_amount;
            Protocol: ClaimReceivedSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: ClaimReceivedSplitProof,
            party: Receiver,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Receiver,
            has_balance_decreased: Some(false),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
    };

    test_with_config(false);
    test_with_config(true);
}

#[test]
fn counter_update_txn_by_sender_split_proof() {
    // Sender's counter-decrement (balance unchanged) built jointly by host + secure device (holds sk); covers both
    // parallel (W2) and sequential (W3) flows and both asset-id modes.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_s_scalar = sk_s.0;
    let sk_s_e_scalar = sk_s_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 50;
    account.counter = 1;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();
        let (split_proof, nullifier, _host_proof_time) = gen_split_proof!(
            no_amount;
            Protocol: SenderCounterUpdateSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: SenderCounterUpdateSplitProof,
            party: Sender,
            has_balance_changed: false,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Sender,
            has_balance_decreased: None,
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; no_amount;
            Protocol: SenderCounterUpdateSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: SenderCounterUpdateSplitProof,
            party: Sender,
            has_balance_changed: false,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Sender,
            has_balance_decreased: None,
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
    };

    test_with_config(false);
    test_with_config(true);
}

#[test]
fn reverse_send_txn_split_proof() {
    // Sender's send-reversal (counter down + amount restored to balance) built jointly by host + secure device;
    // covers both parallel (W2) and sequential (W3) flows and both asset-id modes.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_s_scalar = sk_s.0;
    let sk_s_e_scalar = sk_s_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 200;
    account.counter += 1;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_reversing_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();
        let (split_proof, nullifier, _host_proof_time) = gen_split_proof!(
            with_amount;
            Protocol: SenderReverseSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: SenderReverseSplitProof,
            party: Sender,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Sender,
            has_balance_decreased: Some(false),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; with_amount;
            Protocol: SenderReverseSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: SenderReverseSplitProof,
            party: Sender,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Sender,
            has_balance_decreased: Some(false),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
    };

    test_with_config(false);
    test_with_config(true);
}

#[test]
fn reverse_receive_txn_split_proof() {
    // Receiver's receive-reversal (just decrements the pending counter, balance unchanged) built jointly by host +
    // secure device; covers both parallel (W2) and sequential (W3) flows and both asset-id modes.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_r_scalar = sk_r.0;
    let sk_r_e_scalar = sk_r_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    account.balance = 50;
    account.counter = 1;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();
        let (split_proof, nullifier, _host_proof_time) = gen_split_proof!(
            no_amount;
            Protocol: ReceiverCounterUpdateSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: ReceiverCounterUpdateSplitProof,
            party: Receiver,
            has_balance_changed: false,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Receiver,
            has_balance_decreased: None,
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; no_amount;
            Protocol: ReceiverCounterUpdateSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: ReceiverCounterUpdateSplitProof,
            party: Receiver,
            has_balance_changed: false,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Receiver,
            has_balance_decreased: None,
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
    };

    test_with_config(false);
    test_with_config(true);
}

#[test]
fn irreversible_send_txn_split_proof() {
    // Sender's IRREVERSIBLE send (amount deducted immediately, no counter for later reversal) built jointly by host
    // + secure device; covers both parallel (W2) and sequential (W3) flows and both asset-id modes.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_s_scalar = sk_s.0;
    let sk_s_e_scalar = sk_s_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_irreversible_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();
        let (split_proof, nullifier, _host_proof_time) = gen_split_proof!(
            with_amount;
            Protocol: IrreversibleAffirmAsSenderSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: IrreversibleAffirmAsSenderSplitProof,
            party: Sender,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Sender,
            has_balance_decreased: Some(true),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; with_amount;
            Protocol: IrreversibleAffirmAsSenderSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: IrreversibleAffirmAsSenderSplitProof,
            party: Sender,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s_scalar,
            sk_e_scalar: sk_s_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Sender,
            has_balance_decreased: Some(true),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
    };

    test_with_config(false);
    test_with_config(true);
}

#[test]
fn irreversible_receive_txn_split_proof() {
    // Receiver's IRREVERSIBLE receive (amount credited immediately, no separate claim step) built jointly by host +
    // secure device; covers both parallel (W2) and sequential (W3) flows and both asset-id modes.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let sk_r_scalar = sk_r.0;
    let sk_r_e_scalar = sk_r_e.0;
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let mut test_with_config = |reveal_asset_id: bool| {
        let nonce = b"test-nonce";
        let updated_account = account.get_state_for_irreversible_receive(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
            &mut rng,
            reveal_asset_id,
            pk_a_e.0,
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            account_comm_key.clone(),
            enc_gen,
            updated_account_comm,
            &account_tree,
        );
        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();
        let (split_proof, nullifier, _host_proof_time) = gen_split_proof!(
            with_amount;
            Protocol: IrreversibleAffirmAsReceiverSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: IrreversibleAffirmAsReceiverSplitProof,
            party: Receiver,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path.clone(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );

        let (even_tuple, odd_tuple) = verify_split_proof!(
            proof: split_proof,
            party: Receiver,
            has_balance_decreased: Some(false),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();

        // Sequential flow
        let (split_proof_seq, nullifier_seq, _) = gen_split_proof!(
            sequential; with_amount;
            Protocol: IrreversibleAffirmAsReceiverSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: IrreversibleAffirmAsReceiverSplitProof,
            party: Receiver,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r_scalar,
            sk_e_scalar: sk_r_e_scalar,
            b_blinding: b_blinding,
            reveal_asset_id: reveal_asset_id,
        );
        let (even_tuple_seq, odd_tuple_seq) = verify_split_proof!(
            sequential;
            proof: split_proof_seq,
            party: Receiver,
            has_balance_decreased: Some(false),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier_seq,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even_tuple_seq, odd_tuple_seq, &account_tree_params)
            .unwrap();
    };

    test_with_config(false);
    test_with_config(true);
}

#[test]
fn single_shot_settlement_split_proof() {
    // single_shot_settlement (irreversible 1-shot leg) but BOTH the sender and receiver irreversible affirmations
    // are device/host split proofs; hidden asset-id (LegCreationProof + asset curve tree).
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;
    let asset_tree_height = 4;
    let account_tree_height = 6;

    let mut rng = rand::thread_rng();
    let (account_tree_params, account_comm_key, enc_gen) =
        setup_gens_new::<NUM_GENS>(b"test_settlement");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    // Asset tree uses the swapped (Vesta/Pallas) curve pair.
    let asset_tree_params = SelRerandProofParametersNew::<
        VestaParameters,
        PallasParameters,
        VestaParams,
        PallasParams,
    >::new(NUM_GENS as u32, NUM_GENS as u32)
    .unwrap();

    let asset_comm_params = AssetCommitmentParams::new(
        b"asset-comm-params",
        1,
        0,
        &account_tree_params.odd_parameters.bp_gens(),
    );

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );
    let sk_s_scalar = sk_s.0;
    let sk_s_e_scalar = sk_s_e.0;
    let sk_r_scalar = sk_r.0;
    let sk_r_e_scalar = sk_r_e.0;

    let asset_id: AssetId = 1;
    let amount: Balance = 50;

    // Build a deterministic asset tree (commitment does not depend on reveal_asset_id).
    let asset_data_for_tree =
        AssetData::new(asset_id, vec![pk_a_e.0], vec![], &asset_comm_params).unwrap();
    let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
        &vec![asset_data_for_tree.commitment],
        &asset_tree_params,
        Some(asset_tree_height),
    );
    let asset_tree_root = asset_tree.root_node();

    // Create sender and receiver accounts.
    let sender_id = PallasFr::rand(&mut rng);
    let (mut sender_account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, sender_id);
    sender_account.balance = 200;

    let receiver_id = PallasFr::rand(&mut rng);
    let (mut receiver_account, _, _, _) =
        new_account(&mut rng, asset_id, pk_r, pk_r_e, receiver_id);
    receiver_account.balance = 150;

    // Two-account tree (sender at index 0, receiver at index 1).
    let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();
    let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &vec![sender_account_comm.0, receiver_account_comm.0],
        &account_tree_params,
        Some(account_tree_height),
    );
    let account_tree_root = account_tree.root_node();

    let updated_sender_account = sender_account
        .get_state_for_irreversible_send(amount)
        .unwrap();
    let updated_sender_account_comm = updated_sender_account
        .commit(account_comm_key.clone())
        .unwrap();

    let updated_receiver_account = receiver_account
        .get_state_for_irreversible_receive(amount)
        .unwrap();
    let updated_receiver_account_comm = updated_receiver_account
        .commit(account_comm_key.clone())
        .unwrap();

    println!(
        "For L={L}, asset tree height = {asset_tree_height}, account tree height = {account_tree_height}"
    );

    let mut test_with_config = |reveal_asset_id: bool| {
        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id,
        };

        let (leg, leg_enc, leg_enc_rand) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        let nonce = b"single_shot_settlement_split_proof_nonce";

        // asset_path is consumed by LegCreationProof::new; obtain fresh each time.
        let asset_path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        // Clone the asset_data deterministically (same inputs, same commitment).
        let asset_data =
            AssetData::new(asset_id, vec![pk_a_e.0], vec![], &asset_comm_params).unwrap();

        let start = Instant::now();
        let settlement_proof =
            LegCreationProof::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>::new::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                leg.clone(),
                leg_enc.clone(),
                leg_enc_rand.clone(),
                asset_path,
                asset_data,
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            )
            .unwrap();
        println!("Settlement creation time: {:?}", start.elapsed());

        // Sender split proof
        let (leg_enc_core_s, eph_pk_s) = leg_enc.core_and_eph_keys_for_sender();
        let k_1_s = PallasFr::rand(&mut rng);
        let k_asset_id_s = if !reveal_asset_id {
            Some(PallasFr::rand(&mut rng))
        } else {
            None
        };

        let start = Instant::now();
        let (protocol_s, mut even_prover_s, odd_prover_s, sender_nullifier) =
            IrreversibleAffirmAsSenderSplitProtocol::<
                L,
                PallasFr,
                VestaFr,
                PallasParameters,
                VestaParameters,
            >::init::<_, PallasParams, VestaParams>(
                &mut rng,
                (leg_enc_core_s.clone(), eph_pk_s.clone(), amount),
                &sender_account,
                &updated_sender_account,
                updated_sender_account_comm,
                account_tree.get_path_to_leaf_for_proof(0, 0).unwrap(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                k_1_s,
                k_asset_id_s,
            )
            .unwrap();

        let (challenge_h_s, re_randomized_leaf_s, auth_rerandomization_s, auth_rand_new_comm_s) =
            extract_prover_challenge_and_data!(even_prover_s, protocol_s);

        let auth_proof_s = AuthProofAffirmation::new(
            &mut rng,
            sk_s_scalar,
            sk_s_e_scalar,
            auth_rerandomization_s,
            auth_rand_new_comm_s,
            vec![k_1_s],
            if !reveal_asset_id {
                vec![k_asset_id_s.unwrap()]
            } else {
                vec![]
            },
            vec![LegProverConfig {
                encryption: leg_enc_core_s.clone(),
                party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s.clone()),
                amount,
                has_balance_changed: true,
            }],
            &re_randomized_leaf_s,
            &updated_sender_account_comm.0,
            sender_nullifier,
            nonce,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
            b_blinding,
            enc_gen,
        )
        .unwrap();

        let (host_s, balance_s) = protocol_s
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_s,
                even_prover_s,
                odd_prover_s,
                &account_tree_params,
                &mut rng,
            )
            .unwrap();
        let sender_split_proof =
            IrreversibleAffirmAsSenderSplitProof::assemble(host_s, balance_s, auth_proof_s);
        println!("Sender split proof creation time: {:?}", start.elapsed());

        // Receiver split proof
        let (leg_enc_core_r, eph_pk_r) = leg_enc.core_and_eph_keys_for_receiver();
        let k_1_r = PallasFr::rand(&mut rng);
        let k_asset_id_r = if !reveal_asset_id {
            Some(PallasFr::rand(&mut rng))
        } else {
            None
        };

        let start = Instant::now();
        let (protocol_r, mut even_prover_r, odd_prover_r, receiver_nullifier) =
            IrreversibleAffirmAsReceiverSplitProtocol::<
                L,
                PallasFr,
                VestaFr,
                PallasParameters,
                VestaParameters,
            >::init::<_, PallasParams, VestaParams>(
                &mut rng,
                (leg_enc_core_r.clone(), eph_pk_r.clone(), amount),
                &receiver_account,
                &updated_receiver_account,
                updated_receiver_account_comm,
                account_tree.get_path_to_leaf_for_proof(1, 0).unwrap(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                k_1_r,
                k_asset_id_r,
            )
            .unwrap();

        let (challenge_h_r, re_randomized_leaf_r, auth_rerandomization_r, auth_rand_new_comm_r) =
            extract_prover_challenge_and_data!(even_prover_r, protocol_r);

        let auth_proof_r = AuthProofAffirmation::new(
            &mut rng,
            sk_r_scalar,
            sk_r_e_scalar,
            auth_rerandomization_r,
            auth_rand_new_comm_r,
            vec![k_1_r],
            if !reveal_asset_id {
                vec![k_asset_id_r.unwrap()]
            } else {
                vec![]
            },
            vec![LegProverConfig {
                encryption: leg_enc_core_r.clone(),
                party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r.clone()),
                amount,
                has_balance_changed: true,
            }],
            &re_randomized_leaf_r,
            &updated_receiver_account_comm.0,
            receiver_nullifier,
            nonce,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
            b_blinding,
            enc_gen,
        )
        .unwrap();

        let (host_data_r, balance_r) = protocol_r
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_r,
                even_prover_r,
                odd_prover_r,
                &account_tree_params,
                &mut rng,
            )
            .unwrap();
        let receiver_split_proof =
            IrreversibleAffirmAsReceiverSplitProof::assemble(host_data_r, balance_r, auth_proof_r);
        println!("Receiver split proof creation time: {:?}", start.elapsed());

        // Verify all three proofs and batch-verify the BP tuples --------------
        let start = Instant::now();

        // Settlement proof uses the asset tree (Vesta=G0/even, Pallas=G1/odd).
        // Account proofs use the account tree (Pallas=G0/even, Vesta=G1/odd).
        // So settlement_even ↔ Vesta, but account even ↔ Pallas; swap when batching.
        let (settlement_even, settlement_odd) = settlement_proof
            .verify_and_return_tuples(
                leg_enc.clone(),
                &asset_tree_root,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                account_comm_key.sk_enc_gen(),
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let (sender_even, sender_odd) = verify_split_proof!(
            proof: sender_split_proof,
            party: Sender,
            has_balance_decreased: Some(true),
            updated_account_comm: updated_sender_account_comm,
            nullifier: sender_nullifier,
            root: &account_tree_root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core_s,
            eph_pk: &eph_pk_s,
            b_blinding: b_blinding,
            rng: &mut rng,
        );

        let (receiver_even, receiver_odd) = verify_split_proof!(
            proof: receiver_split_proof,
            party: Receiver,
            has_balance_decreased: Some(false),
            updated_account_comm: updated_receiver_account_comm,
            nullifier: receiver_nullifier,
            root: &account_tree_root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core_r,
            eph_pk: &eph_pk_r,
            b_blinding: b_blinding,
            rng: &mut rng,
        );

        println!("tuples time: {:?}", start.elapsed());

        // settlement_odd  = Pallas tuple, goes with Pallas-even account tuples
        // settlement_even = Vesta  tuple, goes with Vesta-odd  account tuples
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

        let settlement_proof_size = settlement_proof.compressed_size() + leg_enc.compressed_size();
        let sender_proof_size = sender_split_proof.compressed_size();
        let receiver_proof_size = receiver_split_proof.compressed_size();

        println!(
            "settlement={settlement_proof_size}B, sender={sender_proof_size}B, receiver={receiver_proof_size}B"
        );
        println!("verifier time = {verifier_time:?}");
    };

    // LegCreationProof requires a hidden asset-id; the reveal_asset_id=true
    // variant would use PublicAssetLegCreationProof and is a separate test.
    test_with_config(false);
}

#[test]
fn single_shot_settlement_asset_id_revealed_split_proof() {
    // single_shot_settlement_split_proof with public asset-id: device/host split sender+receiver affirmations, but
    // the leg uses a single-curve PublicAssetLegCreationProof (no asset curve tree).
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;
    let account_tree_height = 6;

    let mut rng = rand::thread_rng();
    let (account_tree_params, account_comm_key, enc_gen) =
        setup_gens_new::<NUM_GENS>(b"test_public_asset_settlement");

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let leaf_level_pc_gens = PedersenGens::<Affine<PallasParameters>>::default();
    let leaf_level_bp_gens = BulletproofGens::<Affine<PallasParameters>>::new(NUM_GENS as u32, 1);

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) =
        setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );
    let sk_s_scalar = sk_s.0;
    let sk_s_e_scalar = sk_s_e.0;
    let sk_r_scalar = sk_r.0;
    let sk_r_e_scalar = sk_r_e.0;

    let asset_id: AssetId = 1;
    let amount: Balance = 50;

    let (leg, leg_enc, leg_enc_rand) = setup_public_asset_leg(
        &mut rng,
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );

    let sender_id = PallasFr::rand(&mut rng);
    let (mut sender_account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, sender_id);
    sender_account.balance = 200;

    let receiver_id = PallasFr::rand(&mut rng);
    let (mut receiver_account, _, _, _) =
        new_account(&mut rng, asset_id, pk_r, pk_r_e, receiver_id);
    receiver_account.balance = 150;

    let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();
    let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();
    let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
        &vec![sender_account_comm.0, receiver_account_comm.0],
        &account_tree_params,
        Some(account_tree_height),
    );
    let account_tree_root = account_tree.root_node();

    let updated_sender_account = sender_account
        .get_state_for_irreversible_send(amount)
        .unwrap();
    let updated_sender_account_comm = updated_sender_account
        .commit(account_comm_key.clone())
        .unwrap();

    let updated_receiver_account = receiver_account
        .get_state_for_irreversible_receive(amount)
        .unwrap();
    let updated_receiver_account_comm = updated_receiver_account
        .commit(account_comm_key.clone())
        .unwrap();

    let nonce = b"single_shot_settlement_asset_id_revealed_split_proof_nonce";

    println!("For L={L}, account tree height = {account_tree_height}, asset_id revealed");

    let start = Instant::now();
    let settlement_proof = PublicAssetLegCreationProof::<PallasParameters>::new(
        &mut rng,
        leg.clone(),
        leg_enc.clone(),
        leg_enc_rand.clone(),
        nonce,
        &leaf_level_pc_gens,
        &leaf_level_bp_gens,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    )
    .unwrap();
    println!("Settlement creation time: {:?}", start.elapsed());

    let (leg_enc_core_s, eph_pk_s) = leg_enc.core_and_eph_keys_for_sender();
    let k_1_s = PallasFr::rand(&mut rng);

    let start = Instant::now();
    let (protocol_s, mut even_prover_s, odd_prover_s, sender_nullifier) =
        IrreversibleAffirmAsSenderSplitProtocol::<
            L,
            PallasFr,
            VestaFr,
            PallasParameters,
            VestaParameters,
        >::init::<_, PallasParams, VestaParams>(
            &mut rng,
            (leg_enc_core_s.clone(), eph_pk_s.clone(), amount),
            &sender_account,
            &updated_sender_account,
            updated_sender_account_comm,
            account_tree.get_path_to_leaf_for_proof(0, 0).unwrap(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            k_1_s,
            None,
        )
        .unwrap();

    let (challenge_h_s, re_randomized_leaf_s, auth_rerandomization_s, auth_rand_new_comm_s) =
        extract_prover_challenge_and_data!(even_prover_s, protocol_s);

    let auth_proof_s = AuthProofAffirmation::new(
        &mut rng,
        sk_s_scalar,
        sk_s_e_scalar,
        auth_rerandomization_s,
        auth_rand_new_comm_s,
        vec![k_1_s],
        vec![],
        vec![LegProverConfig {
            encryption: leg_enc_core_s.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s.clone()),
            amount,
            has_balance_changed: true,
        }],
        &re_randomized_leaf_s,
        &updated_sender_account_comm.0,
        sender_nullifier,
        nonce,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
        b_blinding,
        enc_gen,
    )
    .unwrap();

    let (host_s, balance_s) = protocol_s
        .gen_proof::<_, PallasParams, VestaParams>(
            &challenge_h_s,
            even_prover_s,
            odd_prover_s,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
    let sender_split_proof =
        IrreversibleAffirmAsSenderSplitProof::assemble(host_s, balance_s, auth_proof_s);
    println!("Sender split proof creation time: {:?}", start.elapsed());

    let (leg_enc_core_r, eph_pk_r) = leg_enc.core_and_eph_keys_for_receiver();
    let k_1_r = PallasFr::rand(&mut rng);

    let start = Instant::now();
    let (protocol_r, mut even_prover_r, odd_prover_r, receiver_nullifier) =
        IrreversibleAffirmAsReceiverSplitProtocol::<
            L,
            PallasFr,
            VestaFr,
            PallasParameters,
            VestaParameters,
        >::init::<_, PallasParams, VestaParams>(
            &mut rng,
            (leg_enc_core_r.clone(), eph_pk_r.clone(), amount),
            &receiver_account,
            &updated_receiver_account,
            updated_receiver_account_comm,
            account_tree.get_path_to_leaf_for_proof(1, 0).unwrap(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            k_1_r,
            None,
        )
        .unwrap();

    let (challenge_h_r, re_randomized_leaf_r, auth_rerandomization_r, auth_rand_new_comm_r) =
        extract_prover_challenge_and_data!(even_prover_r, protocol_r);

    let auth_proof_r = AuthProofAffirmation::new(
        &mut rng,
        sk_r_scalar,
        sk_r_e_scalar,
        auth_rerandomization_r,
        auth_rand_new_comm_r,
        vec![k_1_r],
        vec![],
        vec![LegProverConfig {
            encryption: leg_enc_core_r.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r.clone()),
            amount,
            has_balance_changed: true,
        }],
        &re_randomized_leaf_r,
        &updated_receiver_account_comm.0,
        receiver_nullifier,
        nonce,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
        b_blinding,
        enc_gen,
    )
    .unwrap();

    let (host_data_r, balance_r) = protocol_r
        .gen_proof::<_, PallasParams, VestaParams>(
            &challenge_h_r,
            even_prover_r,
            odd_prover_r,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
    let receiver_split_proof =
        IrreversibleAffirmAsReceiverSplitProof::assemble(host_data_r, balance_r, auth_proof_r);
    println!("Receiver split proof creation time: {:?}", start.elapsed());

    let start = Instant::now();

    settlement_proof
        .verify(
            &mut rng,
            leg_enc.clone(),
            leg_enc.asset_id().unwrap(),
            vec![leg.enc_keys[0]],
            vec![],
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            account_comm_key.sk_enc_gen(),
            enc_gen,
            None,
        )
        .unwrap();

    let (sender_even, sender_odd) = verify_split_proof!(
        proof: sender_split_proof,
        party: Sender,
        has_balance_decreased: Some(true),
        updated_account_comm: updated_sender_account_comm,
        nullifier: sender_nullifier,
        root: &account_tree_root,
        nonce: nonce,
        account_tree_params: &account_tree_params,
        account_comm_key: &account_comm_key,
        enc_gen: enc_gen,
        leg_enc_core: &leg_enc_core_s,
        eph_pk: &eph_pk_s,
        b_blinding: b_blinding,
        rng: &mut rng,
    );

    let (receiver_even, receiver_odd) = verify_split_proof!(
        proof: receiver_split_proof,
        party: Receiver,
        has_balance_decreased: Some(false),
        updated_account_comm: updated_receiver_account_comm,
        nullifier: receiver_nullifier,
        root: &account_tree_root,
        nonce: nonce,
        account_tree_params: &account_tree_params,
        account_comm_key: &account_comm_key,
        enc_gen: enc_gen,
        leg_enc_core: &leg_enc_core_r,
        eph_pk: &eph_pk_r,
        b_blinding: b_blinding,
        rng: &mut rng,
    );

    println!("tuples time: {:?}", start.elapsed());

    let even_tuples = vec![sender_even, receiver_even];
    let odd_tuples = vec![sender_odd, receiver_odd];

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

    let settlement_proof_size = settlement_proof.compressed_size() + leg_enc.compressed_size();
    let sender_proof_size = sender_split_proof.compressed_size();
    let receiver_proof_size = receiver_split_proof.compressed_size();

    println!(
        "settlement={settlement_proof_size}B, sender={sender_proof_size}B, receiver={receiver_proof_size}B"
    );
    println!("verifier time = {verifier_time:?}");
}

// Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

/// Build a correct sender-affirmation split proof using `protocol` and `auth_proof`.
/// Used by the W2/W3 consistency tests to avoid duplicating the proof assembly logic.
fn make_sender_split_proof(
    rng: &mut impl CryptoRngCore,
    amount: Balance,
    leg_enc_core: &LegEncryptionCore<PallasA>,
    eph_pk: &SenderEphemeralPublicKey<PallasA>,
    account: &AccountState<PallasA>,
    updated_account: &AccountState<PallasA>,
    updated_account_comm: AccountStateCommitment<PallasA>,
    path: CurveTreeWitnessPath<64, PallasParameters, VestaParameters>,
    root: &Root<64, 1, PallasParameters, VestaParameters>,
    nonce: &[u8],
    account_tree_params: &SelRerandProofParametersNew<
        PallasParameters,
        VestaParameters,
        PallasParams,
        VestaParams,
    >,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    enc_gen: PallasA,
    sk: PallasFr,
    sk_e: PallasFr,
) -> (
    AffirmAsSenderSplitProof<64, PallasFr, VestaFr, PallasParameters, VestaParameters>,
    PallasA,
) {
    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
    let k_1 = PallasFr::rand(rng);
    let (protocol, mut even_prover, odd_prover, nullifier) = AffirmAsSenderSplitProtocol::<
        64,
        PallasFr,
        VestaFr,
        PallasParameters,
        VestaParameters,
    >::init::<_, PallasParams, VestaParams>(
        rng,
        (leg_enc_core.clone(), eph_pk.clone(), amount),
        account,
        updated_account,
        updated_account_comm,
        path,
        root,
        nonce,
        account_tree_params,
        account_comm_key.clone(),
        enc_gen,
        k_1,
        None, // asset_id revealed
    )
    .unwrap();
    let (challenge_h, re_randomized_leaf, auth_rerandomization, auth_rand_new_comm) =
        extract_prover_challenge_and_data!(even_prover, protocol);
    let auth_proof = AuthProofAffirmation::new(
        rng,
        sk,
        sk_e,
        auth_rerandomization,
        auth_rand_new_comm,
        vec![k_1],
        vec![],
        vec![LegProverConfig {
            encryption: leg_enc_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
            amount,
            has_balance_changed: true,
        }],
        &re_randomized_leaf,
        &updated_account_comm.0,
        nullifier,
        nonce,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
        b_blinding,
        enc_gen,
    )
    .unwrap();
    let (host, balance) = protocol
        .gen_proof::<_, PallasParams, VestaParams>(
            &challenge_h,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )
        .unwrap();
    (
        AffirmAsSenderSplitProof::assemble(host, balance, auth_proof),
        nullifier,
    )
}

/// Build a correct receiver-affirmation split proof. Asset-id is revealed.
fn make_receiver_split_proof(
    rng: &mut impl CryptoRngCore,
    amount: Balance,
    leg_enc_core: &LegEncryptionCore<PallasA>,
    eph_pk: &ReceiverEphemeralPublicKey<PallasA>,
    account: &AccountState<PallasA>,
    updated_account: &AccountState<PallasA>,
    updated_account_comm: AccountStateCommitment<PallasA>,
    path: CurveTreeWitnessPath<64, PallasParameters, VestaParameters>,
    root: &Root<64, 1, PallasParameters, VestaParameters>,
    nonce: &[u8],
    account_tree_params: &SelRerandProofParametersNew<
        PallasParameters,
        VestaParameters,
        PallasParams,
        VestaParams,
    >,
    account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
    enc_gen: PallasA,
    sk: PallasFr,
    sk_e: PallasFr,
) -> (
    AffirmAsReceiverSplitProof<64, PallasFr, VestaFr, PallasParameters, VestaParameters>,
    PallasA,
) {
    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
    // asset_id is revealed -> ct_amount is always needed; generate k_amount
    let k_amount = PallasFr::rand(rng);
    let (protocol, mut even_prover, odd_prover, nullifier) = AffirmAsReceiverSplitProtocol::<
        64,
        PallasFr,
        VestaFr,
        PallasParameters,
        VestaParameters,
    >::init::<_, PallasParams, VestaParams>(
        rng,
        (leg_enc_core.clone(), eph_pk.clone(), amount),
        account,
        updated_account,
        updated_account_comm,
        path,
        root,
        nonce,
        account_tree_params,
        account_comm_key.clone(),
        enc_gen,
        None, // asset_id revealed
        k_amount,
    )
    .unwrap();
    let (challenge_h, re_randomized_leaf, auth_rerandomization, auth_rand_new_comm) =
        extract_prover_challenge_and_data!(even_prover, protocol);
    let auth_proof = AuthProofAffirmation::new(
        rng,
        sk,
        sk_e,
        auth_rerandomization,
        auth_rand_new_comm,
        vec![k_amount], // revealed leg -> needs k_amount for ct_amount
        vec![],
        vec![LegProverConfig {
            encryption: leg_enc_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk.clone()),
            amount,
            has_balance_changed: false,
        }],
        &re_randomized_leaf,
        &updated_account_comm.0,
        nullifier,
        nonce,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
        b_blinding,
        enc_gen,
    )
    .unwrap();
    let host_data = protocol
        .gen_proof::<_, PallasParams, VestaParams>(
            &challenge_h,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )
        .unwrap();
    (
        AffirmAsReceiverSplitProof::assemble(host_data, auth_proof),
        nullifier,
    )
}

/// Verify a sender split proof (W2 path) using the given leg enc/eph_pk and nonce.
/// Returns `Ok((even, odd))` on success or propagates the error.
fn verify_sender_split(
    rng: &mut impl CryptoRngCore,
    proof: &AffirmAsSenderSplitProof<64, PallasFr, VestaFr, PallasParameters, VestaParameters>,
    leg_enc_core: &LegEncryptionCore<PallasA>,
    eph_pk: &SenderEphemeralPublicKey<PallasA>,
    updated_account_comm: AccountStateCommitment<PallasA>,
    nullifier: PallasA,
    root: &Root<64, 1, PallasParameters, VestaParameters>,
    nonce: &[u8],
    account_tree_params: &SelRerandProofParametersNew<
        PallasParameters,
        VestaParameters,
        PallasParams,
        VestaParams,
    >,
    account_comm_key: &impl AccountCommitmentKeyTrait<PallasA>,
    enc_gen: PallasA,
) -> Result<()> {
    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
    let mut verifier = proof
        .challenge_contribution::<PallasParams, VestaParams>(
            updated_account_comm,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            leg_enc_core,
            eph_pk,
        )
        .unwrap();
    let challenge_h_v = verifier
        .even_verifier
        .as_mut()
        .unwrap()
        .transcript()
        .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
    let re_randomized_leaf_v = proof
        .common
        .partial
        .re_randomized_path
        .as_ref()
        .unwrap()
        .path
        .get_rerandomized_leaf()
        .unwrap();
    proof.common.auth_proof.verify(
        vec![LegVerifierConfig {
            encryption: leg_enc_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
            has_balance_decreased: Some(true),
            has_counter_decreased: None,
        }],
        &re_randomized_leaf_v,
        &updated_account_comm.0,
        nullifier,
        nonce,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
        b_blinding,
        enc_gen,
        None,
    )?;
    let (even_tuple, odd_tuple) = proof
        .verify_and_return_tuples::<_, PallasParams, VestaParams>(
            verifier,
            &challenge_h_v,
            updated_account_comm,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rng,
            None,
        )
        .unwrap();
    verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params)
}

/// Verify a receiver split proof (W2 path) using the given leg enc/eph_pk and nonce.
fn verify_receiver_split(
    rng: &mut impl CryptoRngCore,
    proof: &AffirmAsReceiverSplitProof<64, PallasFr, VestaFr, PallasParameters, VestaParameters>,
    leg_enc_core: &LegEncryptionCore<PallasA>,
    eph_pk: &ReceiverEphemeralPublicKey<PallasA>,
    updated_account_comm: AccountStateCommitment<PallasA>,
    nullifier: PallasA,
    root: &Root<64, 1, PallasParameters, VestaParameters>,
    nonce: &[u8],
    account_tree_params: &SelRerandProofParametersNew<
        PallasParameters,
        VestaParameters,
        PallasParams,
        VestaParams,
    >,
    account_comm_key: &impl AccountCommitmentKeyTrait<PallasA>,
    enc_gen: PallasA,
) -> Result<()> {
    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
    let mut verifier = proof
        .challenge_contribution::<PallasParams, VestaParams>(
            updated_account_comm,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            leg_enc_core,
            eph_pk,
        )
        .unwrap();
    let challenge_h_v = verifier
        .even_verifier
        .as_mut()
        .unwrap()
        .transcript()
        .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
    let re_randomized_leaf_v = proof
        .common
        .partial
        .re_randomized_path
        .as_ref()
        .unwrap()
        .path
        .get_rerandomized_leaf()
        .unwrap();
    proof.common.auth_proof.verify(
        vec![LegVerifierConfig {
            encryption: leg_enc_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk.clone()),
            has_balance_decreased: None,
            has_counter_decreased: None,
        }],
        &re_randomized_leaf_v,
        &updated_account_comm.0,
        nullifier,
        nonce,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
        b_blinding,
        enc_gen,
        None,
    )?;
    let (even_tuple, odd_tuple) = proof
        .verify_and_return_tuples::<_, PallasParams, VestaParams>(
            verifier,
            &challenge_h_v,
            updated_account_comm,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rng,
            None,
        )
        .unwrap();
    verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params)
}

#[test]
fn sender_affirmation_w2_consistency() {
    // W2: If the verifier uses a different leg (ciphertexts / eph keys)
    // than the device used when building the auth-proof, the transcript diverges and
    // verification must fail. Same for a wrong updated-account-commitment or wrong nonce.

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let nonce = b"w2-sender-test-nonce";

    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    // Build the leg that device and host agree on.
    let (_, leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: true,
        },
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();

    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = make_sender_split_proof(
        &mut rng,
        amount,
        &leg_enc_core,
        &eph_pk,
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
        sk_s.0,
        sk_s_e.0,
    );

    // Correct verification
    verify_sender_split(
        &mut rng,
        &proof,
        &leg_enc_core,
        &eph_pk,
        updated_account_comm,
        nullifier,
        &root,
        nonce,
        &account_tree_params,
        &account_comm_key,
        enc_gen,
    )
    .expect("correct W2 verification must succeed");

    // Wrong leg (different ciphertexts / eph keys)
    let (_, different_leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: true,
        },
        pk_a_e.0,
        None,
        amount + 1, // different amount, different ciphertexts
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (different_leg_enc_core, different_eph_pk) =
        different_leg_enc.core_and_eph_keys_for_sender();
    assert!(
        verify_sender_split(
            &mut rng,
            &proof,
            &different_leg_enc_core,
            &different_eph_pk,
            updated_account_comm,
            nullifier,
            &root,
            nonce,
            &account_tree_params,
            &account_comm_key,
            enc_gen,
        )
        .is_err(),
        "wrong leg must cause verification failure"
    );

    // Wrong updated-account-commitment
    let wrong_uac = AccountStateCommitment(PallasA::rand(&mut rng));
    assert!(
        verify_sender_split(
            &mut rng,
            &proof,
            &leg_enc_core,
            &eph_pk,
            wrong_uac,
            nullifier,
            &root,
            nonce,
            &account_tree_params,
            &account_comm_key,
            enc_gen,
        )
        .is_err(),
        "wrong updated_account_comm must cause verification failure"
    );

    // Wrong nonce
    assert!(
        verify_sender_split(
            &mut rng,
            &proof,
            &leg_enc_core,
            &eph_pk,
            updated_account_comm,
            nullifier,
            &root,
            b"wrong-nonce",
            &account_tree_params,
            &account_comm_key,
            enc_gen,
        )
        .is_err(),
        "wrong nonce must cause verification failure"
    );
}

/// W2: Receiver-affirmation analogue of `sender_affirmation_w2_consistency`.
#[test]
fn receiver_affirmation_w2_consistency() {
    // W2 receiver analogue of sender_affirmation_w2_consistency: if the verifier uses a different leg / updated
    // account-commitment / nonce than the device used to build the auth-proof, the transcript diverges -> must fail.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<64, _>(account_comm, &account_tree_params, 6);

    let nonce = b"w2-receiver-test-nonce";

    let updated_account = account.get_state_for_receive();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let (_, leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: true,
        },
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();

    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = make_receiver_split_proof(
        &mut rng,
        amount,
        &leg_enc_core,
        &eph_pk,
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
        enc_gen,
        sk_r.0,
        sk_r_e.0,
    );

    // Correct verification
    verify_receiver_split(
        &mut rng,
        &proof,
        &leg_enc_core,
        &eph_pk,
        updated_account_comm,
        nullifier,
        &root,
        nonce,
        &account_tree_params,
        &account_comm_key,
        enc_gen,
    )
    .expect("correct W2 receiver verification must succeed");

    // Wrong leg
    let (_, different_leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: true,
        },
        pk_a_e.0,
        None,
        amount + 1,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (different_leg_enc_core, different_eph_pk) =
        different_leg_enc.core_and_eph_keys_for_receiver();
    assert!(
        verify_receiver_split(
            &mut rng,
            &proof,
            &different_leg_enc_core,
            &different_eph_pk,
            updated_account_comm,
            nullifier,
            &root,
            nonce,
            &account_tree_params,
            &account_comm_key,
            enc_gen,
        )
        .is_err(),
        "wrong leg must cause verification failure"
    );

    //  Wrong updated-account-commitment
    let wrong_uac = AccountStateCommitment(PallasA::rand(&mut rng));
    assert!(
        verify_receiver_split(
            &mut rng,
            &proof,
            &leg_enc_core,
            &eph_pk,
            wrong_uac,
            nullifier,
            &root,
            nonce,
            &account_tree_params,
            &account_comm_key,
            enc_gen,
        )
        .is_err(),
        "wrong updated_account_comm must cause verification failure"
    );

    //  Wrong nonce
    assert!(
        verify_receiver_split(
            &mut rng,
            &proof,
            &leg_enc_core,
            &eph_pk,
            updated_account_comm,
            nullifier,
            &root,
            b"wrong-nonce",
            &account_tree_params,
            &account_comm_key,
            enc_gen,
        )
        .is_err(),
        "wrong nonce must cause verification failure"
    );
}

#[test]
fn sender_affirmation_w3_consistency() {
    // W3 (sequential) sender: host emits `challenge_h` to the device; device derives
    // `ledger_nonce = challenge_h || nonce`, produces auth_proof, then feeds its
    // serialised auth_proof back into the host transcript before finalising `challenge_h_final`.
    //
    // Check:
    // - wrong leg given to device, verification must fail.
    // - wrong updated-account-comm given to device, fail.
    // - host gives a different (wrong) challenge to the device, i.e. device builds
    // auth_proof with `wrong_challenge || nonce` but host finalises with the real
    // `challenge_h || auth_proof_bytes`, challenge mismatch, fail.
    // - host does not hash device's auth_proof into its own transcript before
    //    deriving `challenge_h_final`, decoupled challenges, fail.

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");
    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let nonce = b"w3-sender-test-nonce";

    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let (_, leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: true,
        },
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();

    let path_factory = || account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    // Helper: run the sequential (W3) prover and return (proof, nullifier).
    // `device_challenge_h` is the challenge the host sends to the device (may be tampered).
    // `host_feeds_auth_into_transcript` controls whether the host hashes the auth_proof.
    let run_w3 = |device_challenge_h: PallasFr,
                  host_feeds_auth: bool,
                  device_leg_enc_core: &LegEncryptionCore<PallasA>,
                  device_eph_pk: &SenderEphemeralPublicKey<PallasA>|
     -> (
        AffirmAsSenderSplitProof<64, PallasFr, VestaFr, PallasParameters, VestaParameters>,
        PallasA,
    ) {
        let mut local_rng = rand::thread_rng();
        let k_1 = PallasFr::rand(&mut local_rng);
        let (protocol, mut even_prover, odd_prover, nullifier) = AffirmAsSenderSplitProtocol::<
            64,
            PallasFr,
            VestaFr,
            PallasParameters,
            VestaParameters,
        >::init::<_, PallasParams, VestaParams>(
            &mut local_rng,
            (device_leg_enc_core.clone(), device_eph_pk.clone(), amount),
            &account,
            &updated_account,
            updated_account_comm,
            path_factory(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            k_1,
            None,
        )
        .unwrap();

        // Device builds ledger_nonce = device_challenge_h || nonce
        let mut ch_bytes = Vec::new();
        device_challenge_h
            .serialize_compressed(&mut ch_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = ch_bytes.iter().chain(nonce.iter()).copied().collect();

        let re_randomized_leaf = protocol.rerandomized_leaf();
        let auth_rerandomization = protocol.auth_rerandomization();
        let auth_rand_new_comm = protocol.auth_rand_new_comm();

        let auth_proof = AuthProofAffirmation::new(
            &mut local_rng,
            sk_s.0,
            sk_s_e.0,
            auth_rerandomization,
            auth_rand_new_comm,
            vec![k_1],
            vec![],
            vec![LegProverConfig {
                encryption: device_leg_enc_core.clone(),
                party_eph_pk: PartyEphemeralPublicKey::Sender(device_eph_pk.clone()),
                amount,
                has_balance_changed: true,
            }],
            &re_randomized_leaf,
            &updated_account_comm.0,
            nullifier,
            &ledger_nonce,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
            b_blinding,
            enc_gen,
        )
        .unwrap();

        // Host: optionally hash auth_proof into transcript before deriving final challenge
        if host_feeds_auth {
            let mut auth_bytes = Vec::new();
            auth_proof.serialize_compressed(&mut auth_bytes).unwrap();
            even_prover
                .transcript()
                .append_message(b"auth-proof", &auth_bytes);
        }
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

        let (host, balance) = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_final,
                even_prover,
                odd_prover,
                &account_tree_params,
                &mut local_rng,
            )
            .unwrap();

        (
            AffirmAsSenderSplitProof::assemble(host, balance, auth_proof),
            nullifier,
        )
    };

    //  1. Correct W3 flow
    {
        let (split_proof, nullifier, _) = gen_split_proof!(
            sequential; with_amount;
            Protocol: AffirmAsSenderSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: AffirmAsSenderSplitProof,
            party: Sender,
            has_balance_changed: true,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path_factory(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_s.0,
            sk_e_scalar: sk_s_e.0,
            b_blinding: b_blinding,
            reveal_asset_id: true,
        );
        let (even, odd) = verify_split_proof!(
            sequential;
            proof: split_proof,
            party: Sender,
            has_balance_decreased: Some(true),
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even, odd, &account_tree_params)
            .expect("correct W3 sender must verify");
    }

    // For the tampered cases we need the real challenge_h to pass to run_w3.
    // Obtain it from a fresh host init.
    let real_challenge_h = {
        let k_1 = PallasFr::rand(&mut rng);
        let (_, mut even_prover, _, _) = AffirmAsSenderSplitProtocol::<
            64,
            PallasFr,
            VestaFr,
            PallasParameters,
            VestaParameters,
        >::init::<_, PallasParams, VestaParams>(
            &mut rng,
            (leg_enc_core.clone(), eph_pk.clone(), amount),
            &account,
            &updated_account,
            updated_account_comm,
            path_factory(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            k_1,
            None,
        )
        .unwrap();
        even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
    };

    //  2. Wrong leg given to device
    {
        let (_, different_leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            LegEncConfig {
                parties_see_each_other: true,
                reveal_asset_id: true,
            },
            pk_a_e.0,
            None,
            amount + 1,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );
        let (diff_core, diff_eph) = different_leg_enc.core_and_eph_keys_for_sender();
        let (proof, nullifier) = run_w3(real_challenge_h, true, &diff_core, &diff_eph);
        // Use auth_proof verify directly (the device used diff_core but verifier uses leg_enc_core).
        let ch_v = {
            let k_1 = PallasFr::rand(&mut rng);
            let (_, mut ep, _, _) = AffirmAsSenderSplitProtocol::<
                64,
                PallasFr,
                VestaFr,
                PallasParameters,
                VestaParameters,
            >::init::<_, PallasParams, VestaParams>(
                &mut rng,
                (leg_enc_core.clone(), eph_pk.clone(), amount),
                &account,
                &updated_account,
                updated_account_comm,
                path_factory(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                k_1,
                None,
            )
            .unwrap();
            ep.transcript()
                .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
        };
        let mut ch_v_bytes = Vec::new();
        ch_v.serialize_compressed(&mut ch_v_bytes).unwrap();
        let ledger_nonce_v: Vec<u8> = ch_v_bytes.iter().chain(nonce.iter()).copied().collect();
        let re_leaf = proof
            .common
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf()
            .unwrap();
        assert!(
            proof
                .common
                .auth_proof
                .verify(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_core.clone(), // correct leg
                        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
                        has_balance_decreased: Some(true),
                        has_counter_decreased: None,
                    }],
                    &re_leaf,
                    &updated_account_comm.0,
                    nullifier,
                    &ledger_nonce_v,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    None,
                )
                .is_err(),
            "wrong leg in device auth_proof must fail auth verification"
        );
    }

    //  3. Wrong updated-account-comm given to device
    {
        // Device uses wrong uac in auth_proof; but host_protocol was started with correct uac.
        // We simulate this by building auth_proof with a random updated_account_comm.0,
        // checking that auth_proof.verify rejects it on the verifier side.
        let wrong_uac = AccountStateCommitment(PallasA::rand(&mut rng));
        let k_1 = PallasFr::rand(&mut rng);
        let (protocol, mut even_prover, odd_prover, nullifier) = AffirmAsSenderSplitProtocol::<
            64,
            PallasFr,
            VestaFr,
            PallasParameters,
            VestaParameters,
        >::init::<_, PallasParams, VestaParams>(
            &mut rng,
            (leg_enc_core.clone(), eph_pk.clone(), amount),
            &account,
            &updated_account,
            updated_account_comm, // host uses correct uac
            path_factory(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            k_1,
            None,
        )
        .unwrap();
        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let mut ch_bytes = Vec::new();
        challenge_h.serialize_compressed(&mut ch_bytes).unwrap();
        let ledger_nonce: Vec<u8> = ch_bytes.iter().chain(nonce.iter()).copied().collect();
        let re_leaf = protocol.rerandomized_leaf();
        let auth_rerandomization = protocol.auth_rerandomization();
        let auth_rand_new_comm = protocol.auth_rand_new_comm();
        // Device uses wrong_uac.0 in its auth_proof
        let auth_proof_wrong_uac = AuthProofAffirmation::new(
            &mut rng,
            sk_s.0,
            sk_s_e.0,
            auth_rerandomization,
            auth_rand_new_comm,
            vec![k_1],
            vec![],
            vec![LegProverConfig {
                encryption: leg_enc_core.clone(),
                party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
                amount,
                has_balance_changed: true,
            }],
            &re_leaf,
            &wrong_uac.0, // device uses wrong uac
            nullifier,
            &ledger_nonce,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
            b_blinding,
            enc_gen,
        )
        .unwrap();
        let mut auth_bytes = Vec::new();
        auth_proof_wrong_uac
            .serialize_compressed(&mut auth_bytes)
            .unwrap();
        even_prover
            .transcript()
            .append_message(b"auth-proof", &auth_bytes);
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let (host, balance) = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_final,
                even_prover,
                odd_prover,
                &account_tree_params,
                &mut rng,
            )
            .unwrap();
        let proof = AffirmAsSenderSplitProof::assemble(host, balance, auth_proof_wrong_uac);

        // Verifier uses correct updated_account_comm, device's auth_proof was built with wrong uac
        //, transcript diverges, auth_proof.verify must fail.
        let mut verifier_state = proof
            .challenge_contribution::<PallasParams, VestaParams>(
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                &account_comm_key,
                enc_gen,
                &leg_enc_core,
                &eph_pk,
            )
            .unwrap();
        let challenge_h_v = verifier_state
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let mut ch_v_bytes = Vec::new();
        challenge_h_v.serialize_compressed(&mut ch_v_bytes).unwrap();
        let ledger_nonce_v: Vec<u8> = ch_v_bytes.iter().chain(nonce.iter()).copied().collect();
        let re_leaf_v = proof
            .common
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf()
            .unwrap();
        assert!(
            proof
                .common
                .auth_proof
                .verify(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
                        has_balance_decreased: Some(true),
                        has_counter_decreased: None,
                    }],
                    &re_leaf_v,
                    &updated_account_comm.0, // correct uac
                    nullifier,
                    &ledger_nonce_v,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    None,
                )
                .is_err(),
            "wrong updated_account_comm in device auth_proof must fail auth verification"
        );
    }

    //  4. Host gives wrong challenge to device
    // Device builds auth_proof with `wrong_challenge || nonce`; host's prover was
    // initialised with a different state so its real challenge_h != wrong_challenge.
    // The verifier derives the correct challenge_h_v; the ledger_nonce_v won't match.
    {
        let wrong_challenge = PallasFr::rand(&mut rng);
        let (proof, nullifier) = run_w3(wrong_challenge, true, &leg_enc_core, &eph_pk);

        // Reconstruct verifier challenge independently.
        let mut verifier_state = proof
            .challenge_contribution::<PallasParams, VestaParams>(
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                &account_comm_key,
                enc_gen,
                &leg_enc_core,
                &eph_pk,
            )
            .unwrap();
        let challenge_h_v = verifier_state
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let mut ch_v_bytes = Vec::new();
        challenge_h_v.serialize_compressed(&mut ch_v_bytes).unwrap();
        let ledger_nonce_v: Vec<u8> = ch_v_bytes.iter().chain(nonce.iter()).copied().collect();
        let re_leaf_v = proof
            .common
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf()
            .unwrap();
        assert!(
            proof
                .common
                .auth_proof
                .verify(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
                        has_balance_decreased: Some(true),
                        has_counter_decreased: None,
                    }],
                    &re_leaf_v,
                    &updated_account_comm.0,
                    nullifier,
                    &ledger_nonce_v,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    None,
                )
                .is_err(),
            "wrong host challenge to device must cause auth verification failure"
        );
    }

    // 5. Host does NOT hash device's auth_proof into transcript
    // challenge_h_final == challenge_h, so the host sigma responses are computed
    // for challenge_h but the verifier expects them for challenge_h_final_v
    // (derived after hashing the auth_proof). The BP proof will fail to verify.
    {
        let (proof, nullifier) = run_w3(
            real_challenge_h,
            false, /* no auth hash */
            &leg_enc_core,
            &eph_pk,
        );
        // The sequential verifier does hash auth_proof; its challenge_h_final_v ≠ challenge_h.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (even, odd) = verify_split_proof!(
                sequential;
                proof: proof,
                party: Sender,
                has_balance_decreased: Some(true),
                updated_account_comm: updated_account_comm,
                nullifier: nullifier,
                root: &root,
                nonce: nonce,
                account_tree_params: &account_tree_params,
                account_comm_key: &account_comm_key,
                enc_gen: enc_gen,
                leg_enc_core: &leg_enc_core,
                eph_pk: &eph_pk,
                b_blinding: b_blinding,
                rng: &mut rng,
            );
            verify_given_verification_tuples(even, odd, &account_tree_params)
        }));
        // Should either panic (macro's .unwrap()) or return an Err
        assert!(
            result.is_err() || result.unwrap().is_err(),
            "host skipping auth_proof hash must cause verification failure"
        );
    }
}

#[test]
fn receiver_affirmation_w3_consistency() {
    // W3 (sequential) receiver: analogous to `sender_affirmation_w3_consistency`
    // but for the receiver side. Tests wrong leg and wrong updated-account-comm only
    // (the challenge / auth-hash cases are symmetric and already covered by the sender test).

    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    const L: usize = 64;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");
    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let asset_id: AssetId = 1;
    let amount: Balance = 100;

    let id = PallasFr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let account_tree = get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

    let nonce = b"w3-receiver-test-nonce";

    let updated_account = account.get_state_for_receive();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let (_, leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: true,
        },
        pk_a_e.0,
        None,
        amount,
        asset_id,
        pk_s_e.0,
        pk_r_e.0,
        account_comm_key.sk_enc_gen(),
        enc_gen,
    );
    let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();

    let path_factory = || account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    // 1. Correct W3 flow
    {
        let (split_proof, nullifier, _) = gen_split_proof!(
            sequential; no_amount;
            Protocol: AffirmAsReceiverSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
            Proof: AffirmAsReceiverSplitProof,
            party: Receiver,
            has_balance_changed: false,
            rng: &mut rng,
            amount: amount,
            leg_enc_core: leg_enc_core,
            eph_pk: eph_pk,
            old_account: account,
            updated_account: updated_account,
            updated_account_comm: updated_account_comm,
            path: path_factory(),
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: account_comm_key,
            enc_gen: enc_gen,
            sk_scalar: sk_r.0,
            sk_e_scalar: sk_r_e.0,
            b_blinding: b_blinding,
            reveal_asset_id: true,
        );
        let (even, odd) = verify_split_proof!(
            sequential;
            proof: split_proof,
            party: Receiver,
            has_balance_decreased: None,
            updated_account_comm: updated_account_comm,
            nullifier: nullifier,
            root: &root,
            nonce: nonce,
            account_tree_params: &account_tree_params,
            account_comm_key: &account_comm_key,
            enc_gen: enc_gen,
            leg_enc_core: &leg_enc_core,
            eph_pk: &eph_pk,
            b_blinding: b_blinding,
            rng: &mut rng,
        );
        verify_given_verification_tuples(even, odd, &account_tree_params)
            .expect("correct W3 receiver must verify");
    }

    // Derive a reference challenge_h for tampered cases.
    let reference_challenge_h = {
        let k_amount_ref = PallasFr::rand(&mut rng);
        let (_, mut ep, _, _) = AffirmAsReceiverSplitProtocol::<
            64,
            PallasFr,
            VestaFr,
            PallasParameters,
            VestaParameters,
        >::init::<_, PallasParams, VestaParams>(
            &mut rng,
            (leg_enc_core.clone(), eph_pk.clone(), amount),
            &account,
            &updated_account,
            updated_account_comm,
            path_factory(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            None,
            k_amount_ref,
        )
        .unwrap();
        ep.transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
    };

    // Helper: build a W3 receiver proof with a given device-side leg and challenge.
    let run_w3_recv = |device_challenge_h: PallasFr,
                       host_feeds_auth: bool,
                       dev_leg_enc_core: &LegEncryptionCore<PallasA>,
                       dev_eph_pk: &ReceiverEphemeralPublicKey<PallasA>|
     -> (
        AffirmAsReceiverSplitProof<64, PallasFr, VestaFr, PallasParameters, VestaParameters>,
        PallasA,
    ) {
        let mut local_rng = rand::thread_rng();
        let k_amount_local = PallasFr::rand(&mut local_rng);
        let (protocol, mut even_prover, odd_prover, nullifier) = AffirmAsReceiverSplitProtocol::<
            64,
            PallasFr,
            VestaFr,
            PallasParameters,
            VestaParameters,
        >::init::<_, PallasParams, VestaParams>(
            &mut local_rng,
            (dev_leg_enc_core.clone(), dev_eph_pk.clone(), amount),
            &account,
            &updated_account,
            updated_account_comm,
            path_factory(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
            None,
            k_amount_local,
        )
        .unwrap();
        let mut ch_bytes = Vec::new();
        device_challenge_h
            .serialize_compressed(&mut ch_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = ch_bytes.iter().chain(nonce.iter()).copied().collect();
        let re_leaf = protocol.rerandomized_leaf();
        let auth_rerandomization = protocol.auth_rerandomization();
        let auth_rand_new_comm = protocol.auth_rand_new_comm();
        let auth_proof = AuthProofAffirmation::new(
            &mut local_rng,
            sk_r.0,
            sk_r_e.0,
            auth_rerandomization,
            auth_rand_new_comm,
            vec![k_amount_local], // revealed leg -> needs k_amount for ct_amount
            vec![],
            vec![LegProverConfig {
                encryption: dev_leg_enc_core.clone(),
                party_eph_pk: PartyEphemeralPublicKey::Receiver(dev_eph_pk.clone()),
                amount,
                has_balance_changed: false,
            }],
            &re_leaf,
            &updated_account_comm.0,
            nullifier,
            &ledger_nonce,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
            b_blinding,
            enc_gen,
        )
        .unwrap();
        if host_feeds_auth {
            let mut ab = Vec::new();
            auth_proof.serialize_compressed(&mut ab).unwrap();
            even_prover.transcript().append_message(b"auth-proof", &ab);
        }
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let host_data = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_final,
                even_prover,
                odd_prover,
                &account_tree_params,
                &mut local_rng,
            )
            .unwrap();
        (
            AffirmAsReceiverSplitProof::assemble(host_data, auth_proof),
            nullifier,
        )
    };

    // 2. Wrong leg given to device
    {
        let (_, diff_leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            LegEncConfig {
                parties_see_each_other: true,
                reveal_asset_id: true,
            },
            pk_a_e.0,
            None,
            amount + 1,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );
        let (diff_core, diff_eph) = diff_leg_enc.core_and_eph_keys_for_receiver();
        let (proof, nullifier) = run_w3_recv(reference_challenge_h, true, &diff_core, &diff_eph);

        let mut vs = proof
            .challenge_contribution::<PallasParams, VestaParams>(
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                &account_comm_key,
                enc_gen,
                &leg_enc_core,
                &eph_pk,
            )
            .unwrap();
        let ch_v = vs
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let mut ch_v_bytes = Vec::new();
        ch_v.serialize_compressed(&mut ch_v_bytes).unwrap();
        let ln_v: Vec<u8> = ch_v_bytes.iter().chain(nonce.iter()).copied().collect();
        let re_leaf_v = proof
            .common
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf()
            .unwrap();
        assert!(
            proof
                .common
                .auth_proof
                .verify(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk.clone()),
                        has_balance_decreased: None,
                        has_counter_decreased: None,
                    }],
                    &re_leaf_v,
                    &updated_account_comm.0,
                    nullifier,
                    &ln_v,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    None,
                )
                .is_err(),
            "wrong leg in W3 receiver must fail auth verification"
        );
    }

    // 3. Host gives wrong challenge to device
    {
        let wrong_challenge = PallasFr::rand(&mut rng);
        let (proof, nullifier) = run_w3_recv(wrong_challenge, true, &leg_enc_core, &eph_pk);

        let mut vs = proof
            .challenge_contribution::<PallasParams, VestaParams>(
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                &account_comm_key,
                enc_gen,
                &leg_enc_core,
                &eph_pk,
            )
            .unwrap();
        let ch_v = vs
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);
        let mut ch_v_bytes = Vec::new();
        ch_v.serialize_compressed(&mut ch_v_bytes).unwrap();
        let ln_v: Vec<u8> = ch_v_bytes.iter().chain(nonce.iter()).copied().collect();
        let re_leaf_v = proof
            .common
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf()
            .unwrap();
        assert!(
            proof
                .common
                .auth_proof
                .verify(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk.clone()),
                        has_balance_decreased: None,
                        has_counter_decreased: None,
                    }],
                    &re_leaf_v,
                    &updated_account_comm.0,
                    nullifier,
                    &ln_v,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    None,
                )
                .is_err(),
            "wrong host challenge to device must cause W3 receiver auth failure"
        );
    }

    // 4. Host does NOT hash auth_proof into transcript
    {
        let (proof, nullifier) = run_w3_recv(reference_challenge_h, false, &leg_enc_core, &eph_pk);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let (even, odd) = verify_split_proof!(
                sequential;
                proof: proof,
                party: Receiver,
                has_balance_decreased: None,
                updated_account_comm: updated_account_comm,
                nullifier: nullifier,
                root: &root,
                nonce: nonce,
                account_tree_params: &account_tree_params,
                account_comm_key: &account_comm_key,
                enc_gen: enc_gen,
                leg_enc_core: &leg_enc_core,
                eph_pk: &eph_pk,
                b_blinding: b_blinding,
                rng: &mut rng,
            );
            verify_given_verification_tuples(even, odd, &account_tree_params)
        }));
        assert!(
            result.is_err() || result.unwrap().is_err(),
            "host skipping auth_proof hash must cause W3 receiver verification failure"
        );
    }
}

#[cfg(feature = "ignore_prover_input_sanitation")]
mod input_sanitation_disabled {
    use super::*;
    use crate::Error;
    use crate::account::AccountCommitmentKeyTrait;
    use crate::account::tests::{get_tree_with_account_comm, setup_gens_new, setup_leg};
    use crate::account::{
        AffirmAsReceiverTxnProof, AffirmAsSenderTxnProof, ClaimReceivedTxnProof,
        IrreversibleAffirmAsReceiverTxnProof, IrreversibleAffirmAsSenderTxnProof,
        ReceiverCounterUpdateTxnProof, SenderCounterUpdateTxnProof, SenderReverseTxnProof,
    };
    use crate::account_registration::tests::new_account;
    use crate::leg::tests::setup_keys;
    use ark_pallas::Fr as PallasFr;
    use ark_std::UniformRand;

    macro_rules! assert_account_verify_fails_with_rmc {
        (
            $proof:expr,
            $rng:expr,
            $leg:expr,
            $root:expr,
            $updated_account_comm:expr,
            $nullifier:expr,
            $nonce:expr,
            $account_tree_params:expr,
            $account_comm_key:expr,
            $enc_gen:expr $(,)?
        ) => {{
            let verify_without_rmc = $proof.verify(
                $rng,
                $leg,
                $root,
                $updated_account_comm,
                $nullifier,
                $nonce,
                $account_tree_params,
                $account_comm_key.clone(),
                $enc_gen,
                None,
            );
            assert!(verify_without_rmc.is_err());

            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand($rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand($rng));
            let verify_result = $proof.verify(
                $rng,
                $leg,
                $root,
                $updated_account_comm,
                $nullifier,
                $nonce,
                $account_tree_params,
                $account_comm_key.clone(),
                $enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            );
            let rmc_result = verify_rmc(rmc_0, rmc_1);
            assert!(verify_result.is_err() || rmc_result.is_err());
        }};
    }

    #[test]
    fn keep_balance_same_in_send_txn() {
        // A sender account sends AffirmAsSenderTxnProof but does not decrease the balance from his account. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((_sk_r, _pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Create an updated account that doesn't decrease the balance
        let mut updated_account = account.get_state_for_send(amount).unwrap();
        updated_account.balance = account.balance; // Keep same balance

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );

        // Create an updated account that instead increases the balance
        let mut updated_account = account.get_state_for_send(amount).unwrap();
        updated_account.balance = account.balance + amount; // Increase balance

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );
    }

    #[test]
    fn increase_balance_in_receive_txn() {
        // A receiver account sends AffirmAsReceiverTxnProof but increases the balance. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((_sk_s, _pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Create a malicious updated account that increases balance
        let mut updated_account = account.get_state_for_receive();
        updated_account.balance = account.balance + amount;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_receiver(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );
    }

    #[test]
    fn increase_balance_incorrectly_during_claiming_received_funds() {
        // A receiver account sends ClaimReceivedTxnProof but increases the balance more than the actual claim amount. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((_sk_s, _pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
        // Assume that account had some balance and it had sent the receive transaction to increase its counter
        account.balance = 200;
        account.counter += 2;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Update account that increases balance more than the actual claim amount
        let mut updated_account = account.get_state_for_claiming_received(amount).unwrap();
        updated_account.balance = account.balance + 75; // Add extra on top of the actual amount

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = ClaimReceivedTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_receiver(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );

        // Update account with counter decreased by 1 more than it should be
        let mut updated_account = account.get_state_for_claiming_received(amount).unwrap();
        updated_account.counter -= 1;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = ClaimReceivedTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_r.0,
                sk_r_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_receiver(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );
    }

    #[test]
    fn increase_balance_in_counter_update_by_sender() {
        // A sender account sends SenderCounterUpdateTxnProof but increases their balance when it should remain the same. This proof should fail
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((_sk_r, _pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Sender account with non-zero counter
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
        account.balance = 50;
        account.counter = 2;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Update account that increases balance when it should remain the same
        let mut updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        updated_account.balance = account.balance + amount;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderCounterUpdateTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );

        // Update account with counter decreased by 1 more than it should be
        let mut updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        updated_account.counter -= 1;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderCounterUpdateTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );
    }

    #[test]
    fn incorrect_updates_in_reverse_send_txn() {
        // A sender account sends SenderReverseTxnProof but makes incorrect updates to balance or counter. These proofs should fail
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((_sk_r, _pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
        // Assume that account had some balance and it had sent the send transaction to increase its counter
        account.balance = 200;
        account.counter += 2;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let nonce = b"test-nonce";

        // Update account that increases balance more than required
        let mut updated_account = account.get_state_for_reversing_send(amount).unwrap();
        updated_account.balance = account.balance + 50; // Add extra on top of the actual amount

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderReverseTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );

        // Update account with counter decreased by 1 more than it should be
        let mut updated_account = account.get_state_for_reversing_send(amount).unwrap();
        updated_account.counter -= 1;

        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) = SenderReverseTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            {
                let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                (c, e, amount)
            },
            AccountTxnWitness::new(
                sk_s.0,
                sk_s_e.0,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
            ),
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_gen,
        )
        .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &root,
            updated_account_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );
    }

    #[test]
    fn incorrect_updates_in_single_shot_settlement() {
        // Test malicious updates in single shot settlement (irreversible send/receive)
        // These proofs should fail because balance or counter updates are incorrect
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        let (((sk_s, pk_s), (sk_s_e, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
            setup_keys(
                &mut rng,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
            );

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Create sender account
        let sender_id = PallasFr::rand(&mut rng);
        let (mut sender_account, _, _, _) =
            new_account(&mut rng, asset_id, pk_s, pk_s_e, sender_id);
        sender_account.balance = 200; // Ensure sufficient balance
        sender_account.counter = 5; // Set non-zero counter for testing
        let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

        // Create receiver account
        let receiver_id = PallasFr::rand(&mut rng);
        let (mut receiver_account, _, _, _) =
            new_account(&mut rng, asset_id, pk_r, pk_r_e, receiver_id);
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

        let (proof, nullifier) =
            IrreversibleAffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    sender_account.clone(),
                    malicious_sender_account.clone(),
                    malicious_sender_comm,
                ),
                sender_path.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            malicious_sender_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
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

        let (proof, nullifier) =
            IrreversibleAffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    receiver_account.clone(),
                    malicious_receiver_account.clone(),
                    malicious_receiver_comm,
                ),
                receiver_path.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            malicious_receiver_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );

        // Sender trying to decrease counter
        let mut malicious_sender_account = sender_account
            .get_state_for_irreversible_send(amount)
            .unwrap();
        malicious_sender_account.counter -= 1;

        let malicious_sender_comm = malicious_sender_account
            .commit(account_comm_key.clone())
            .unwrap();

        let (proof, nullifier) =
            IrreversibleAffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    sender_account.clone(),
                    malicious_sender_account.clone(),
                    malicious_sender_comm,
                ),
                sender_path.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_sender(),
            &account_tree_root,
            malicious_sender_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );

        // Receiver trying to decrease counter
        let mut malicious_receiver_account = receiver_account
            .get_state_for_irreversible_receive(amount)
            .unwrap();
        malicious_receiver_account.counter -= 1;

        let malicious_receiver_comm = malicious_receiver_account
            .commit(account_comm_key.clone())
            .unwrap();

        let (proof, nullifier) =
            IrreversibleAffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    receiver_account.clone(),
                    malicious_receiver_account.clone(),
                    malicious_receiver_comm,
                ),
                receiver_path,
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_receiver(),
            &account_tree_root,
            malicious_receiver_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );
    }

    #[test]
    fn incorrect_updates_in_receiver_counter_update() {
        // A receiver account sends ReceiverCounterUpdateTxnProof but makes incorrect updates.
        // These proofs should fail verification.
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");
        let (
            ((_sk_s, _pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, _) = setup_leg(
            &mut rng,
            pk_a_e.0,
            None,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Receiver account with counter > 0 from previous receive affirmations.
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
        account.balance = 200;
        account.counter = 2;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();
        let nonce = b"test-nonce";

        // ReceiverCounterUpdate should NOT change balance; force it to increase.
        let mut updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        updated_account.balance = account.balance + 50;
        let updated_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let (proof, nullifier) =
            ReceiverCounterUpdateTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    account.clone(),
                    updated_account.clone(),
                    updated_comm,
                ),
                path.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof,
            &mut rng,
            leg_enc.core_and_eph_keys_for_receiver(),
            &root,
            updated_comm,
            nullifier,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );

        // Counter decreased by 2 instead of 1 (too much).
        let mut updated_account2 = account.get_state_for_decreasing_counter(None).unwrap();
        updated_account2.counter = account.counter - 2; // should be counter - 1
        let updated_comm2 = updated_account2.commit(account_comm_key.clone()).unwrap();

        let (proof2, nullifier2) =
            ReceiverCounterUpdateTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    account.clone(),
                    updated_account2.clone(),
                    updated_comm2,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

        assert_account_verify_fails_with_rmc!(
            proof2,
            &mut rng,
            leg_enc.core_and_eph_keys_for_receiver(),
            &root,
            updated_comm2,
            nullifier2,
            nonce,
            &account_tree_params,
            account_comm_key,
            enc_gen,
        );
    }

    #[cfg(feature = "nightly_mocking_tests")]
    mod mocking_tests {
        use super::*;
        use crate::account::common::CommonAffirmationSplitProtocol;
        use crate::account::state::NUM_GENERATORS;
        use crate::util::{
            create_bp_and_null_t_values, create_leg_link_t_values, enforce_balance_change_prover,
        };
        use mocktopus::mocking::{MockResult, Mockable};

        struct MockGuard {
            clear_fn: fn(),
        }

        impl MockGuard {
            fn new(clear_fn: fn()) -> Self {
                Self { clear_fn }
            }
        }

        impl Drop for MockGuard {
            fn drop(&mut self) {
                (self.clear_fn)();
            }
        }

        fn clear_create_bp_and_null_t_values_mock() {
            create_bp_and_null_t_values::<
                rand::rngs::ThreadRng,
                PallasFr,
                PallasParameters,
                [PallasA; NUM_GENERATORS],
            >
                .clear_mock();
        }

        fn clear_balance_change_amount_mocks() {
            enforce_balance_change_prover::<rand::rngs::ThreadRng, PallasFr, PallasParameters>
                .clear_mock();
        }

        fn mock_balance_change_amount(amount: Balance) {
            // Make the balance bulletproof commit to a different amount than the leg. The amount
            // response is taken from the leg's amount ciphertext, so the balance arithmetic stays
            // self-consistent and only the check that the balance change equals the leg amount fails.
            enforce_balance_change_prover::<rand::rngs::ThreadRng, PallasFr, PallasParameters>
                .mock_safe(
                    move |rng,
                          old_bal,
                          new_bal,
                          existing_amount,
                          has_balance_decreased,
                          even_prover,
                          bp_gens| {
                        let malicious_amounts = vec![amount; existing_amount.len()];
                        MockResult::Continue((
                            rng,
                            old_bal,
                            new_bal,
                            malicious_amounts,
                            has_balance_decreased,
                            even_prover,
                            bp_gens,
                        ))
                    },
                );
        }

        // All sender/receiver actions use the shared logic so following tests should cover for other txns as well (to an extent)

        #[test]
        fn sender_affirmations_with_mocked_old_rho_fails_verification() {
            // Malicious sender: a mock bumps the prover's old_rho by 1 so it no longer matches the committed
            // account; the rho/nullifier-consistency constraint must make verification fail.
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"mocked-old-rho-in-create-bp-and-null-t-values");

            let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
                setup_keys(
                    &mut rng,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                );

            let asset_id = 1;
            let amount = 100;
            let (_, leg_enc, _) = setup_leg(
                &mut rng,
                pk_a_e.0,
                None,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            );

            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
            account.balance = 200;

            let account_tree = get_tree_with_account_comm::<L, _>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
                6,
            )
            .unwrap();

            let updated_account = account.get_state_for_send(amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();
            let nonce = b"test-nonce";

            create_bp_and_null_t_values::<
                rand::rngs::ThreadRng,
                PallasFr,
                PallasParameters,
                [PallasA; NUM_GENERATORS],
            >
                .mock_safe(
                    move |rng,
                          include_sk,
                          initial_rho,
                          old_rho,
                          new_rho,
                          initial_randomness,
                          old_randomness,
                          new_randomness,
                          initial_rho_blinding,
                          old_rho_blinding,
                          new_rho_blinding,
                          initial_randomness_blinding,
                          old_randomness_blinding,
                          new_randomness_blinding,
                          sk_enc,
                          sk_enc_blinding,
                          sk_enc_inv_blinding,
                          prover,
                          account_comm_key,
                          pc_gens,
                          bp_gens| {
                        MockResult::Continue((
                            rng,
                            include_sk,
                            initial_rho,
                            old_rho + PallasFr::from(1u64),
                            new_rho,
                            initial_randomness,
                            old_randomness,
                            new_randomness,
                            initial_rho_blinding,
                            old_rho_blinding,
                            new_rho_blinding,
                            initial_randomness_blinding,
                            old_randomness_blinding,
                            new_randomness_blinding,
                            sk_enc,
                            sk_enc_blinding,
                            sk_enc_inv_blinding,
                            prover,
                            account_comm_key,
                            pc_gens,
                            bp_gens,
                        ))
                    },
                );
            let _ = &MockGuard::new(clear_create_bp_and_null_t_values_mock);

            let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    account.clone(),
                    updated_account.clone(),
                    updated_account_comm,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

            assert_account_verify_fails_with_rmc!(
                proof,
                &mut rng,
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_gen,
            );
        }

        #[test]
        fn sender_affirmations_with_mocked_new_rho_and_randomness_fails_verification() {
            // Malicious sender: a mock swaps the new account's rho AND randomness for fresh random values, so they
            // don't match the committed updated-account; the consistency constraints must reject it.
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(
                b"mocked-new-rho-randomness-in-create-bp-and-null-t-values",
            );

            let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
                setup_keys(
                    &mut rng,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                );

            let asset_id = 1;
            let amount = 100;
            let (_, leg_enc, _) = setup_leg(
                &mut rng,
                pk_a_e.0,
                None,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            );

            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
            account.balance = 200;

            let account_tree = get_tree_with_account_comm::<L, _>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
                6,
            )
            .unwrap();

            let updated_account = account.get_state_for_send(amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();
            let nonce = b"test-nonce";

            let mocked_new_rho = PallasFr::rand(&mut rng);
            let mocked_new_randomness = PallasFr::rand(&mut rng);

            create_bp_and_null_t_values::<
                rand::rngs::ThreadRng,
                PallasFr,
                PallasParameters,
                [PallasA; NUM_GENERATORS],
            >
                .mock_safe(
                    move |rng,
                          include_sk,
                          initial_rho,
                          old_rho,
                          _new_rho,
                          initial_randomness,
                          old_randomness,
                          _new_randomness,
                          initial_rho_blinding,
                          old_rho_blinding,
                          new_rho_blinding,
                          initial_randomness_blinding,
                          old_randomness_blinding,
                          new_randomness_blinding,
                          sk_enc,
                          sk_enc_blinding,
                          sk_enc_inv_blinding,
                          prover,
                          account_comm_key,
                          pc_gens,
                          bp_gens| {
                        MockResult::Continue((
                            rng,
                            include_sk,
                            initial_rho,
                            old_rho,
                            mocked_new_rho,
                            initial_randomness,
                            old_randomness,
                            mocked_new_randomness,
                            initial_rho_blinding,
                            old_rho_blinding,
                            new_rho_blinding,
                            initial_randomness_blinding,
                            old_randomness_blinding,
                            new_randomness_blinding,
                            sk_enc,
                            sk_enc_blinding,
                            sk_enc_inv_blinding,
                            prover,
                            account_comm_key,
                            pc_gens,
                            bp_gens,
                        ))
                    },
                );
            let _ = &MockGuard::new(clear_create_bp_and_null_t_values_mock);

            let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    account.clone(),
                    updated_account.clone(),
                    updated_account_comm,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

            assert_account_verify_fails_with_rmc!(
                proof,
                &mut rng,
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_gen,
            );
        }

        #[test]
        fn sender_affirmation_with_mocked_smaller_amount_fails_verification() {
            // Malicious sender: leg encrypts 100 but a mock makes the proof deduct only 60 from balance; the
            // constraint binding the balance-change to the leg's encrypted amount must reject the mismatch.
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"mocked-smaller-balance-change-amount-sender");

            let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
                setup_keys(
                    &mut rng,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                );

            let asset_id = 1;
            let honest_amount = 100u64;
            let malicious_amount = 60u64;
            let (_, leg_enc, _) = setup_leg(
                &mut rng,
                pk_a_e.0,
                None,
                honest_amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            );

            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
            account.balance = 200;

            let account_tree = get_tree_with_account_comm::<L, _>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
                6,
            )
            .unwrap();

            let updated_account = account.get_state_for_send(malicious_amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();
            let nonce = b"test-nonce";

            mock_balance_change_amount(malicious_amount);
            let _ = &MockGuard::new(clear_balance_change_amount_mocks);

            let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                    (c, e, honest_amount)
                },
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    account.clone(),
                    updated_account.clone(),
                    updated_account_comm,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

            assert_account_verify_fails_with_rmc!(
                proof,
                &mut rng,
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_gen,
            );
        }

        #[test]
        fn claim_received_with_mocked_larger_amount_fails_verification() {
            // Malicious receiver: leg amount is 100 but a mock makes the claim credit 140 into balance; the
            // constraint binding the claimed balance-change to the leg's encrypted amount must reject the inflation.
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"mocked-larger-balance-change-amount-claim");

            let (
                ((_sk_s, _pk_s), (_sk_s_e, pk_s_e)),
                ((sk_r, pk_r), (sk_r_e, pk_r_e)),
                ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
            ) = setup_keys(
                &mut rng,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
            );

            let asset_id = 1;
            let honest_amount = 100u64;
            let malicious_amount = 140u64;
            let (_, leg_enc, _) = setup_leg(
                &mut rng,
                pk_a_e.0,
                None,
                honest_amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            );

            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
            account.balance = 200;
            account.counter += 2;

            let account_tree = get_tree_with_account_comm::<L, _>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
                6,
            )
            .unwrap();

            let updated_account = account
                .get_state_for_claiming_received(malicious_amount)
                .unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();
            let nonce = b"test-nonce";

            mock_balance_change_amount(malicious_amount);
            let _ = &MockGuard::new(clear_balance_change_amount_mocks);

            let (proof, nullifier) = ClaimReceivedTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                    (c, e, honest_amount)
                },
                AccountTxnWitness::new(
                    sk_r.0,
                    sk_r_e.0,
                    account.clone(),
                    updated_account.clone(),
                    updated_account_comm,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

            assert_account_verify_fails_with_rmc!(
                proof,
                &mut rng,
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_gen,
            );
        }

        fn mock_ct_asset_id(forged_asset_id: AssetId) {
            CommonAffirmationSplitProtocol::<
                64,
                PallasFr,
                VestaFr,
                PallasParameters,
                VestaParameters,
            >::asset_id_proto::<rand::rngs::ThreadRng>
                .mock_safe(
                    move |rng, _asset_id, asset_id_blinding, k_asset_ids, enc_gen, b_blinding| {
                        MockResult::Continue((
                            rng,
                            PallasFr::from(forged_asset_id),
                            asset_id_blinding,
                            k_asset_ids,
                            enc_gen,
                            b_blinding,
                        ))
                    },
                );
        }

        fn clear_ct_asset_id_mocks() {
            CommonAffirmationSplitProtocol::<
                64,
                PallasFr,
                VestaFr,
                PallasParameters,
                VestaParameters,
            >::asset_id_proto::<rand::rngs::ThreadRng>
                .clear_mock();
        }

        fn clear_leg_link_mock() {
            create_leg_link_t_values::<PallasFr, PallasParameters>.clear_mock();
        }

        // Make the solo leg-link amount ciphertext commit to `forged` while the balance change and
        // the leg ciphertext stay honest. This is the other side of mock_balance_change_amount: the
        // lie is in the leg-link instead of the balance proof.
        fn mock_leg_link_amount(forged: Balance) {
            create_leg_link_t_values::<PallasFr, PallasParameters>.mock_safe(
                move |legs,
                      amounts,
                      has_balance_changed,
                      sk_enc_inv,
                      sk_enc_inv_blinding,
                      amount_blindings,
                      asset_id,
                      asset_id_blinding,
                      enc_gen| {
                    // amounts is &[Balance]; leak a forged slice of matching length.
                    let forged_amounts: &'static [Balance] =
                        Box::leak(vec![forged; amounts.len()].into_boxed_slice());
                    MockResult::Continue((
                        legs,
                        forged_amounts,
                        has_balance_changed,
                        sk_enc_inv,
                        sk_enc_inv_blinding,
                        amount_blindings,
                        asset_id,
                        asset_id_blinding,
                        enc_gen,
                    ))
                },
            );
        }

        #[test]
        fn split_sender_affirmation_wrong_amount_and_asset_id_fails_verification() {
            // Malicious sender: leg amount is 100 but tries to reduce only 60
            // In another case sender's asset id is does not match the leg
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"split-wrong-amount-assetid");
            let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

            let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
                setup_keys(
                    &mut rng,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                );

            let account_asset_id: AssetId = 1;
            let honest_amount: Balance = 100;
            let malicious_amount: Balance = 60;
            let forged_asset_id: AssetId = 2;
            let nonce = b"split-wrong-binding-nonce";

            let id = PallasFr::rand(&mut rng);
            let sk_s_scalar = sk_s.0;
            let sk_s_e_scalar = sk_s_e.0;
            let (mut account, _, _, _) = new_account(&mut rng, account_asset_id, pk_s, pk_s_e, id);
            account.balance = 200;
            let account_comm = account.commit(account_comm_key.clone()).unwrap();
            let account_tree =
                get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

            // Malicious sender uses wrong amount
            {
                let updated_account = account.get_state_for_send(malicious_amount).unwrap();
                let updated_account_comm =
                    updated_account.commit(account_comm_key.clone()).unwrap();
                let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
                    &mut rng,
                    false,
                    pk_a_e.0,
                    pk_s_e.0,
                    pk_r_e.0,
                    honest_amount,
                    account_asset_id,
                    account_comm_key.clone(),
                    enc_gen,
                    updated_account_comm,
                    &account_tree,
                );
                let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();

                mock_balance_change_amount(malicious_amount);
                let _guard = MockGuard::new(clear_balance_change_amount_mocks);

                let (split_proof, nullifier, _) = gen_split_proof!(
                    with_amount;
                    Protocol: AffirmAsSenderSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
                    Proof: AffirmAsSenderSplitProof,
                    party: Sender,
                    has_balance_changed: true,
                    rng: &mut rng,
                    amount: honest_amount,
                    leg_enc_core: leg_enc_core,
                    eph_pk: eph_pk,
                    old_account: account,
                    updated_account: updated_account,
                    updated_account_comm: updated_account_comm,
                    path: path,
                    root: &root,
                    nonce: nonce,
                    account_tree_params: &account_tree_params,
                    account_comm_key: account_comm_key,
                    enc_gen: enc_gen,
                    sk_scalar: sk_s_scalar,
                    sk_e_scalar: sk_s_e_scalar,
                    b_blinding: b_blinding,
                    reveal_asset_id: false,
                );

                assert!(
                    split_proof
                        .verify_with_tuples::<_, PallasParams, VestaParams>(
                            updated_account_comm,
                            nullifier,
                            &root,
                            nonce,
                            &account_tree_params,
                            &account_comm_key,
                            enc_gen,
                            &leg_enc_core,
                            &eph_pk,
                            &mut rng,
                            None,
                        )
                        .is_err()
                );
            }

            // Malicious sender uses wrong asset-id
            {
                let updated_account = account.get_state_for_send(honest_amount).unwrap();
                let updated_account_comm =
                    updated_account.commit(account_comm_key.clone()).unwrap();
                let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
                    &mut rng,
                    false,
                    pk_a_e.0,
                    pk_s_e.0,
                    pk_r_e.0,
                    honest_amount,
                    forged_asset_id,
                    account_comm_key.clone(),
                    enc_gen,
                    updated_account_comm,
                    &account_tree,
                );
                let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();

                mock_ct_asset_id(forged_asset_id);
                let _guard = MockGuard::new(clear_ct_asset_id_mocks);

                let (split_proof, nullifier, _) = gen_split_proof!(
                    with_amount;
                    Protocol: AffirmAsSenderSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
                    Proof: AffirmAsSenderSplitProof,
                    party: Sender,
                    has_balance_changed: true,
                    rng: &mut rng,
                    amount: honest_amount,
                    leg_enc_core: leg_enc_core,
                    eph_pk: eph_pk,
                    old_account: account,
                    updated_account: updated_account,
                    updated_account_comm: updated_account_comm,
                    path: path,
                    root: &root,
                    nonce: nonce,
                    account_tree_params: &account_tree_params,
                    account_comm_key: account_comm_key,
                    enc_gen: enc_gen,
                    sk_scalar: sk_s_scalar,
                    sk_e_scalar: sk_s_e_scalar,
                    b_blinding: b_blinding,
                    reveal_asset_id: false,
                );

                assert!(
                    split_proof
                        .verify_with_tuples::<_, PallasParams, VestaParams>(
                            updated_account_comm,
                            nullifier,
                            &root,
                            nonce,
                            &account_tree_params,
                            &account_comm_key,
                            enc_gen,
                            &leg_enc_core,
                            &eph_pk,
                            &mut rng,
                            None,
                        )
                        .is_err()
                );
            }
        }
        #[test]
        fn split_claim_received_wrong_amount_and_asset_id_fails_verification() {
            // Malicious receiver: leg amount is 100 but tries to credit 140 into balance.
            // In another case receiver's asset id does not match the leg
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"split-claim-wrong-amount-assetid");
            let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

            let ((_, (_, pk_s_e)), ((sk_r, pk_r), (sk_r_e, pk_r_e)), (_, (_, pk_a_e))) = setup_keys(
                &mut rng,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
            );

            let account_asset_id: AssetId = 1;
            let honest_amount: Balance = 100;
            let malicious_amount: Balance = 140;
            let forged_asset_id: AssetId = 2;
            let nonce = b"split-claim-wrong-binding-nonce";

            let id = PallasFr::rand(&mut rng);
            let sk_r_scalar = sk_r.0;
            let sk_r_e_scalar = sk_r_e.0;
            let (mut account, _, _, _) = new_account(&mut rng, account_asset_id, pk_r, pk_r_e, id);
            account.balance = 200;
            account.counter += 1;
            let account_comm = account.commit(account_comm_key.clone()).unwrap();
            let account_tree =
                get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

            // Malicious receiver inflates the claimed amount
            {
                let updated_account = account
                    .get_state_for_claiming_received(malicious_amount)
                    .unwrap();
                let updated_account_comm =
                    updated_account.commit(account_comm_key.clone()).unwrap();
                let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
                    &mut rng,
                    false,
                    pk_a_e.0,
                    pk_s_e.0,
                    pk_r_e.0,
                    honest_amount,
                    account_asset_id,
                    account_comm_key.clone(),
                    enc_gen,
                    updated_account_comm,
                    &account_tree,
                );
                let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();

                mock_balance_change_amount(malicious_amount);
                let _guard = MockGuard::new(clear_balance_change_amount_mocks);

                let (split_proof, nullifier, _) = gen_split_proof!(
                    with_amount;
                    Protocol: ClaimReceivedSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
                    Proof: ClaimReceivedSplitProof,
                    party: Receiver,
                    has_balance_changed: true,
                    rng: &mut rng,
                    amount: honest_amount,
                    leg_enc_core: leg_enc_core,
                    eph_pk: eph_pk,
                    old_account: account,
                    updated_account: updated_account,
                    updated_account_comm: updated_account_comm,
                    path: path,
                    root: &root,
                    nonce: nonce,
                    account_tree_params: &account_tree_params,
                    account_comm_key: account_comm_key,
                    enc_gen: enc_gen,
                    sk_scalar: sk_r_scalar,
                    sk_e_scalar: sk_r_e_scalar,
                    b_blinding: b_blinding,
                    reveal_asset_id: false,
                );

                assert!(
                    split_proof
                        .verify_with_tuples::<_, PallasParams, VestaParams>(
                            updated_account_comm,
                            nullifier,
                            &root,
                            nonce,
                            &account_tree_params,
                            &account_comm_key,
                            enc_gen,
                            &leg_enc_core,
                            &eph_pk,
                            &mut rng,
                            None,
                        )
                        .is_err()
                );
            }

            // Malicious receiver uses wrong asset-id
            {
                let updated_account = account
                    .get_state_for_claiming_received(honest_amount)
                    .unwrap();
                let updated_account_comm =
                    updated_account.commit(account_comm_key.clone()).unwrap();
                let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
                    &mut rng,
                    false,
                    pk_a_e.0,
                    pk_s_e.0,
                    pk_r_e.0,
                    honest_amount,
                    forged_asset_id,
                    account_comm_key.clone(),
                    enc_gen,
                    updated_account_comm,
                    &account_tree,
                );
                let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();

                mock_ct_asset_id(forged_asset_id);
                let _guard = MockGuard::new(clear_ct_asset_id_mocks);

                let (split_proof, nullifier, _) = gen_split_proof!(
                    with_amount;
                    Protocol: ClaimReceivedSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
                    Proof: ClaimReceivedSplitProof,
                    party: Receiver,
                    has_balance_changed: true,
                    rng: &mut rng,
                    amount: honest_amount,
                    leg_enc_core: leg_enc_core,
                    eph_pk: eph_pk,
                    old_account: account,
                    updated_account: updated_account,
                    updated_account_comm: updated_account_comm,
                    path: path,
                    root: &root,
                    nonce: nonce,
                    account_tree_params: &account_tree_params,
                    account_comm_key: account_comm_key,
                    enc_gen: enc_gen,
                    sk_scalar: sk_r_scalar,
                    sk_e_scalar: sk_r_e_scalar,
                    b_blinding: b_blinding,
                    reveal_asset_id: false,
                );

                assert!(
                    split_proof
                        .verify_with_tuples::<_, PallasParams, VestaParams>(
                            updated_account_comm,
                            nullifier,
                            &root,
                            nonce,
                            &account_tree_params,
                            &account_comm_key,
                            enc_gen,
                            &leg_enc_core,
                            &eph_pk,
                            &mut rng,
                            None,
                        )
                        .is_err()
                );
            }
        }

        #[test]
        fn leg_link_amount_mismatch_in_send_fails_verification() {
            // The balance honestly decreases by 100 and the leg encrypts 100, but a mock makes the
            // leg-link amount ciphertext commit to 60. The leg amount has to match both the balance
            // change and the leg's own ciphertext, so verification must reject. This is the
            // leg-link-side counterpart of sender_affirmation_with_mocked_smaller_amount.
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"leg-link-amount-mismatch-send");

            let (((sk_s, pk_s), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
                setup_keys(
                    &mut rng,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                );

            let asset_id = 1;
            let honest_amount = 100u64;
            let forged_leg_link_amount = 60u64;
            let (_, leg_enc, _) = setup_leg(
                &mut rng,
                pk_a_e.0,
                None,
                honest_amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            );

            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_s, pk_s_e, id);
            account.balance = 200;
            let account_tree = get_tree_with_account_comm::<L, _>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
                6,
            )
            .unwrap();

            // Honest balance change: decrease by 100 (matches the leg).
            let updated_account = account.get_state_for_send(honest_amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();
            let nonce = b"test-nonce";

            mock_leg_link_amount(forged_leg_link_amount);
            let _guard = MockGuard::new(clear_leg_link_mock);

            let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_sender();
                    (c, e, honest_amount)
                },
                AccountTxnWitness::new(
                    sk_s.0,
                    sk_s_e.0,
                    account.clone(),
                    updated_account.clone(),
                    updated_account_comm,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

            assert_account_verify_fails_with_rmc!(
                proof,
                &mut rng,
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_gen,
            );
        }

        #[test]
        fn revealed_receive_with_leg_link_wrong_enc_key_fails_verification() {
            // A receiver affirming a revealed-asset leg with no balance change must hold the
            // account's encryption key, since the amount ciphertext is the only thing tying the
            // account to the leg. Here the prover uses a different key (the kind of substitution the
            // old participant relation allowed, e.g. the leg randomness r_1); the account commitment
            // binds the real key, so verification must reject.
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"revealed-receive-wrong-enc-key");

            let ((_, (_, pk_s_e)), ((sk_r, pk_r), (_sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
                setup_keys(
                    &mut rng,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                );

            let asset_id = 1;
            let amount = 100u64;

            // Revealed asset-id leg, no balance change -> LegAccountLink::AmountOnly.
            let conf = LegEncConfig {
                parties_see_each_other: true,
                reveal_asset_id: true,
            };
            let (_, leg_enc, _) = setup_leg_with_conf(
                &mut rng,
                conf,
                pk_a_e.0,
                None,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                account_comm_key.sk_enc_gen(),
                enc_gen,
            );

            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
            account.balance = 200;
            let account_tree = get_tree_with_account_comm::<L, _>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
                6,
            )
            .unwrap();

            let updated_account = account.get_state_for_receive();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();
            let nonce = b"test-nonce";

            // The prover does not hold the account's encryption key; this stands in for using the
            // leg randomness r_1 in place of the real key.
            let wrong_sk_enc = PallasFr::rand(&mut rng);

            let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                {
                    let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
                    (c, e, amount)
                },
                AccountTxnWitness::new(
                    sk_r.0,
                    wrong_sk_enc,
                    account.clone(),
                    updated_account.clone(),
                    updated_account_comm,
                ),
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();

            assert_account_verify_fails_with_rmc!(
                proof,
                &mut rng,
                leg_enc.core_and_eph_keys_for_receiver(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_gen,
            );
        }

        #[test]
        fn revealed_receive_split_with_wrong_device_enc_key_fails_verification() {
            // On a revealed-asset receiver affirmation with no balance change, the device builds its
            // half of the amount ciphertext from its encryption key. Here the device is given a key
            // that is not the account's encryption key, so the device half and the host half no
            // longer add up to the leg's amount ciphertext and the account commitment opening also
            // fails; verification must reject.
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12;
            const L: usize = 64;
            let (account_tree_params, account_comm_key, enc_gen) =
                setup_gens_new::<NUM_GENS>(b"revealed-receive-split-wrong-device-key");
            let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

            let ((_, (_, pk_s_e)), ((sk_r, pk_r), (_sk_r_e, pk_r_e)), (_, (_, pk_a_e))) =
                setup_keys(
                    &mut rng,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                );

            let asset_id = 1;
            let amount = 100u64;
            let sk_r_scalar = sk_r.0;
            // The device uses a non-account encryption key.
            let wrong_sk_e_scalar = PallasFr::rand(&mut rng);

            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_r, pk_r_e, id);
            account.balance = 200;
            let account_comm = account.commit(account_comm_key.clone()).unwrap();
            let account_tree =
                get_tree_with_commitment::<L, _>(account_comm, &account_tree_params, 6);

            let updated_account = account.get_state_for_receive();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            // Revealed asset-id leg.
            let (leg_enc, updated_account_comm, path, root) = setup_single_leg_test(
                &mut rng,
                true,
                pk_a_e.0,
                pk_s_e.0,
                pk_r_e.0,
                amount,
                asset_id,
                account_comm_key.clone(),
                enc_gen,
                updated_account_comm,
                &account_tree,
            );
            let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_receiver();

            let nonce = b"test-nonce";
            let (split_proof, nullifier, _) = gen_split_proof!(
                no_amount;
                Protocol: AffirmAsReceiverSplitProtocol::<L, PallasFr, VestaFr, PallasParameters, VestaParameters>,
                Proof: AffirmAsReceiverSplitProof,
                party: Receiver,
                has_balance_changed: false,
                rng: &mut rng,
                amount: amount,
                leg_enc_core: leg_enc_core,
                eph_pk: eph_pk,
                old_account: account,
                updated_account: updated_account,
                updated_account_comm: updated_account_comm,
                path: path,
                root: &root,
                nonce: nonce,
                account_tree_params: &account_tree_params,
                account_comm_key: account_comm_key,
                enc_gen: enc_gen,
                sk_scalar: sk_r_scalar,
                sk_e_scalar: wrong_sk_e_scalar,
                b_blinding: b_blinding,
                reveal_asset_id: true,
            );

            assert!(
                split_proof
                    .verify_with_tuples::<_, PallasParams, VestaParams>(
                        updated_account_comm,
                        nullifier,
                        &root,
                        nonce,
                        &account_tree_params,
                        &account_comm_key,
                        enc_gen,
                        &leg_enc_core,
                        &eph_pk,
                        &mut rng,
                        None,
                    )
                    .is_err()
            );
        }
    }

    // More tests can be added like secret key mismatch, incorrect rho or randomness creation, etc.
}
