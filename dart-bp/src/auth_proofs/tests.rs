use super::*;
use crate::account::tests::{setup_gens_new, setup_leg_with_conf};
use crate::account::{AccountCommitmentKeyTrait, LegProverConfig, LegVerifierConfig};
use crate::account_registration::tests::{new_account, setup_comm_key};
use crate::auth_proofs::account::{AuthProofAffirmation, LegAuthLink, RespAssetId};
use crate::auth_proofs::fee_account::AuthProofFeePayment;
use crate::auth_proofs::transparent::AuthProofTransparent;
use crate::fee_account::tests::new_fee_account;
use crate::keys::{keygen_enc, keygen_sig};
use crate::leg::tests::setup_keys;
use crate::leg::{Leg, LegEncConfig, PartyEphemeralPublicKey, SenderEphemeralPublicKey};
use ark_ec::CurveGroup;
use ark_ec::short_weierstrass::Affine;
use ark_pallas::PallasConfig;
use ark_std::UniformRand;
use polymesh_dart_auth::Error;
use rand::thread_rng;

type Fr = ark_pallas::Fr;
type PallasA = ark_pallas::Affine;

#[test]
fn registration() {
    // Round-trips the registration auth-proof: device proves knowledge of the signing + encryption secret keys behind the registered public keys, and the verifier accepts.
    let mut rng = rand::thread_rng();

    let account_comm_key = setup_comm_key(b"testing");

    // Investor creates keys
    let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());

    let enc_key_gen = account_comm_key.sk_enc_gen();
    let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);

    // Proof done by device
    let nonce = b"test-nonce";

    let proof = AuthProofOnlySks::new(
        &mut rng,
        sk_aff.0,
        sk_enc.0,
        pk_aff.0,
        pk_enc.0,
        nonce,
        &account_comm_key.sk_gen(),
        &account_comm_key.sk_enc_gen(),
    )
    .unwrap();

    proof
        .verify(
            pk_aff.0,
            pk_enc.0,
            nonce,
            &account_comm_key.sk_gen(),
            &account_comm_key.sk_enc_gen(),
            None,
        )
        .unwrap();
}

#[test]
fn fee_payment_auth() {
    // Round-trips the fee-payment auth-proof over the re-randomized old/updated fee-account commitments + nullifier; checks the host/device partial commitments sum to the full ones, and that a wrong nullifier/nonce/old-comm/new-comm each makes verification fail.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2
    // const L: usize = 64;
    let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;

    // All parties generate their keys
    let (((sk_s, pk_s), _), (_, _), _) = setup_keys(
        &mut rng,
        account_comm_key.sk_gen(),
        account_comm_key.sk_enc_gen(),
    );

    let account = new_fee_account(&mut rng, asset_id, pk_s.clone(), 100);
    let account_comm = account.commit(&account_comm_key).unwrap();

    let leaf_blinding = Fr::rand(&mut rng);
    // Curve tree proof will also randomize it this way
    let re_randomized_account_commitment = (account_comm.0
        + (account_tree_params.even_parameters.pc_gens().B_blinding * leaf_blinding))
        .into_affine();

    let updated_account = account.get_state_for_payment(10).unwrap();
    let updated_account_comm = updated_account.commit(&account_comm_key).unwrap();

    // Only hardware (Ledger) knows these
    let rand_1_old = Fr::rand(&mut rng);
    // let rand_1_new = leaf_blinding - rand_1_old;
    let rand_1_new = Fr::rand(&mut rng);
    // let rand_2_new = updated_account.randomness - rand_1_new;

    // Host creates its proof over these commitments. Chain will get these as public input
    let host_commitment_old = (re_randomized_account_commitment
        - pk_s.0
        - (account_tree_params.even_parameters.pc_gens().B_blinding * rand_1_old))
        .into_affine();

    let host_commitment_new = (updated_account_comm.0
        - pk_s.0
        - (account_comm_key.current_randomness_gen() * rand_1_new))
        .into_affine();

    // Creating random nullifier for testing, in practice this should come from host
    let nullifier = PallasA::rand(&mut rng);

    // Proof done by device

    let nonce = b"test-nonce";

    let proof = AuthProofFeePayment::new(
        &mut rng,
        sk_s.0,
        rand_1_old,
        rand_1_new,
        &re_randomized_account_commitment,
        &updated_account_comm.0,
        nullifier,
        nonce,
        account_comm_key.sk_gen(),
        account_comm_key.current_randomness_gen(),
        account_tree_params.even_parameters.pc_gens().B_blinding,
    )
    .unwrap();

    proof
        .verify(
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            account_comm_key.current_randomness_gen(),
            account_tree_params.even_parameters.pc_gens().B_blinding,
            None,
        )
        .unwrap();

    assert_eq!(
        host_commitment_old + proof.partial_re_randomized_account_commitment,
        re_randomized_account_commitment
    );

    assert_eq!(
        host_commitment_new + proof.partial_updated_account_commitment,
        updated_account_comm.0
    );

    let wrong_nullifier = PallasA::rand(&mut rng);
    assert!(
        proof
            .verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                wrong_nullifier,
                nonce,
                account_comm_key.sk_gen(),
                account_comm_key.current_randomness_gen(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
                None,
            )
            .is_err()
    );

    assert!(
        proof
            .verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                b"wrong-nonce",
                account_comm_key.sk_gen(),
                account_comm_key.current_randomness_gen(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
                None,
            )
            .is_err()
    );

    let wrong_re_rand = PallasA::rand(&mut rng);
    assert!(
        proof
            .verify(
                &wrong_re_rand,
                &updated_account_comm.0,
                nullifier,
                nonce,
                account_comm_key.sk_gen(),
                account_comm_key.current_randomness_gen(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
                None,
            )
            .is_err()
    );

    let wrong_updated_comm = PallasA::rand(&mut rng);
    assert!(
        proof
            .verify(
                &re_randomized_account_commitment,
                &wrong_updated_comm,
                nullifier,
                nonce,
                account_comm_key.sk_gen(),
                account_comm_key.current_randomness_gen(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
                None,
            )
            .is_err()
    );
}

#[test]
fn transparent_auth() {
    // Round-trips the transparent (withdraw) auth-proof with two auditor keys; checks partial-commitment sums, that wrong nullifier/nonce/old-comm/new-comm fail, and that each auditor can decrypt its encrypted copy of the signing pubkey.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let enc_key_gen = account_comm_key.sk_enc_gen();

    let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
    let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
    let id = Fr::rand(&mut rng);

    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
    account.balance = 100;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();

    let updated_account = account.get_state_for_withdraw(30).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let leaf_blinding = Fr::rand(&mut rng);
    let pc_gens = account_tree_params.even_parameters.pc_gens();
    let b_blinding = pc_gens.B_blinding;
    let re_randomized_account_commitment =
        (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();

    // Only hardware (Ledger) knows these
    let rand_part_old_comm = Fr::rand(&mut rng);
    let rand_new_comm = Fr::rand(&mut rng);

    let nullifier = PallasA::rand(&mut rng);
    let nonce = b"test-nonce";

    let num_auditor_keys = 2;
    let auditor_keys = (0..num_auditor_keys)
        .map(|_| keygen_enc(&mut rng, enc_key_gen))
        .collect::<Vec<_>>();
    let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

    let proof = AuthProofTransparent::new(
        &mut rng,
        sk_aff.0,
        sk_enc.0,
        rand_part_old_comm,
        rand_new_comm,
        &re_randomized_account_commitment,
        &updated_account_comm.0,
        nullifier,
        auditor_pubkeys.clone(),
        nonce,
        account_comm_key.sk_gen(),
        enc_key_gen,
        b_blinding,
    )
    .unwrap();

    proof
        .verify(
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            &auditor_pubkeys,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            None,
        )
        .unwrap();

    // Verify partial commitments sum correctly
    let pk = pk_aff.0 + pk_enc.0;
    let host_commitment_old =
        (re_randomized_account_commitment - pk - (b_blinding * rand_part_old_comm)).into_affine();
    let host_commitment_new =
        (updated_account_comm.0 - pk - (b_blinding * rand_new_comm)).into_affine();

    assert_eq!(
        host_commitment_old + proof.partial_re_randomized_account_commitment,
        re_randomized_account_commitment
    );
    assert_eq!(
        host_commitment_new + proof.partial_updated_account_commitment,
        updated_account_comm.0
    );

    // Wrong public values: verification must fail in every case because they are
    // committed into the transcript, binding the sigma responses to them.
    let wrong_nullifier = PallasA::rand(&mut rng);
    assert_err!(
        proof.verify(
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            wrong_nullifier,
            &auditor_pubkeys,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            None,
        ),
        Error::SchnorrError(_)
    );

    assert_err!(
        proof.verify(
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            &auditor_pubkeys,
            b"wrong-nonce",
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            None,
        ),
        Error::SchnorrError(_)
    );

    let wrong_re_rand = PallasA::rand(&mut rng);
    assert_err!(
        proof.verify(
            &wrong_re_rand,
            &updated_account_comm.0,
            nullifier,
            &auditor_pubkeys,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            None,
        ),
        Error::SchnorrError(_)
    );

    let wrong_updated_comm = PallasA::rand(&mut rng);
    assert_err!(
        proof.verify(
            &re_randomized_account_commitment,
            &wrong_updated_comm,
            nullifier,
            &auditor_pubkeys,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            None,
        ),
        Error::SchnorrError(_)
    );

    // Verify decryption works
    for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
        assert_eq!(proof.encrypted_pubkeys.decrypt(i, sk.0), pk_aff.0);
    }
}

#[test]
fn affirmation_auth() {
    // Round-trips the affirmation auth-proof for the sender signing off on one leg (balance decreased); checks partial-commitment sums and that a wrong nullifier/nonce fails verification.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let enc_key_gen = account_comm_key.sk_enc_gen();

    let (((sk_aff, pk_aff), (sk_enc, pk_enc)), (_, (_, pk_r_e)), _) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let id = Fr::rand(&mut rng);

    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();

    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

    let leaf_blinding = Fr::rand(&mut rng);
    let re_randomized_account_commitment =
        (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();

    // Auth's shares of the rerandomization
    let rand_part_old_comm = Fr::rand(&mut rng);
    let rand_new_comm = Fr::rand(&mut rng);

    let nullifier = PallasA::rand(&mut rng);
    let nonce = b"test-nonce";

    let conf = LegEncConfig {
        parties_see_each_other: true,
        reveal_asset_id: false,
    };

    let (_, leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        conf,
        pk_enc.0,
        None,
        amount,
        asset_id,
        pk_enc.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );

    let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();

    let k_1 = Fr::rand(&mut rng);
    let k_2 = Fr::rand(&mut rng);

    let legs_prover = vec![LegProverConfig {
        encryption: leg_enc_core.clone(),
        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
        amount,
        has_balance_changed: true,
    }];

    let proof = AuthProofAffirmation::new(
        &mut rng,
        sk_aff.0,
        sk_enc.0,
        rand_part_old_comm,
        rand_new_comm,
        vec![k_1],
        vec![k_2],
        legs_prover,
        &re_randomized_account_commitment,
        &updated_account_comm.0,
        nullifier,
        nonce,
        account_comm_key.sk_gen(),
        enc_key_gen,
        b_blinding,
        enc_gen,
    )
    .unwrap();

    let legs_verifier = vec![LegVerifierConfig {
        encryption: leg_enc_core.clone(),
        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
        has_balance_decreased: Some(true),
        has_counter_decreased: None,
    }];

    proof
        .verify(
            legs_verifier.clone(),
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        )
        .unwrap();

    // Verify partial commitments sum correctly
    let pk = pk_aff.0 + pk_enc.0;
    let host_commitment_old =
        (re_randomized_account_commitment - pk - (b_blinding * rand_part_old_comm)).into_affine();
    let host_commitment_new =
        (updated_account_comm.0 - pk - (b_blinding * rand_new_comm)).into_affine();

    assert_eq!(
        host_commitment_old + proof.partial_re_randomized_account_commitment,
        re_randomized_account_commitment
    );
    assert_eq!(
        host_commitment_new + proof.partial_updated_account_commitment,
        updated_account_comm.0
    );

    let wrong_nullifier = PallasA::rand(&mut rng);
    assert_err!(
        proof.verify(
            legs_verifier.clone(),
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            wrong_nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::SchnorrError(_)
    );

    assert_err!(
        proof.verify(
            legs_verifier.clone(),
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            b"wrong-nonce",
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::SchnorrError(_)
    );

    let wrong_re_rand = PallasA::rand(&mut rng);
    assert_err!(
        proof.verify(
            legs_verifier.clone(),
            &wrong_re_rand,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::SchnorrError(_)
    );

    let wrong_updated_comm = PallasA::rand(&mut rng);
    assert_err!(
        proof.verify(
            legs_verifier.clone(),
            &re_randomized_account_commitment,
            &wrong_updated_comm,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::SchnorrError(_)
    );

    let wrong_legs_verifier = vec![LegVerifierConfig {
        encryption: legs_verifier[0].encryption.clone(),
        party_eph_pk: legs_verifier[0].party_eph_pk.clone(),
        has_balance_decreased: None,
        has_counter_decreased: None,
    }];
    assert_err!(
        proof.verify(
            wrong_legs_verifier,
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::ProofVerificationError(_),
        "Invalid partial_ct_amounts length"
    );

    // Test: verifier uses a different leg encryption than what the prover used.
    // The leg encryption is added to the prover transcript, so a different encryption
    // causes the challenge to diverge and sigma responses to fail verification.
    let (_, different_leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: false,
        },
        pk_enc.0,
        None,
        amount + 1, // different amount → different ciphertexts
        asset_id,
        pk_enc.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );
    let (different_leg_enc_core, different_eph_pk) =
        different_leg_enc.core_and_eph_keys_for_sender();
    let wrong_encryption_legs = vec![LegVerifierConfig {
        encryption: different_leg_enc_core,
        party_eph_pk: PartyEphemeralPublicKey::Sender(different_eph_pk),
        has_balance_decreased: Some(true),
        has_counter_decreased: None,
    }];
    assert_err!(
        proof.verify(
            wrong_encryption_legs,
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::SchnorrError(_)
    );

    let mut truncated_amount_proof = proof.clone();
    truncated_amount_proof.partial_ct_amounts.clear();
    assert_err!(
        truncated_amount_proof.verify(
            legs_verifier.clone(),
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::ProofVerificationError(_),
        "Invalid partial_ct_amounts length"
    );

    let mut truncated_asset_id_proof = proof.clone();
    truncated_asset_id_proof.partial_ct_asset_ids.clear();
    assert_err!(
        truncated_asset_id_proof.verify(
            legs_verifier.clone(),
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::ProofVerificationError(_),
        "Invalid partial_ct_asset_ids length"
    );

    // Verifier receives party_eph_pk with r4 = None while asset-id is hidden; must return Err, not panic.
    let bad_eph_pk =
        PartyEphemeralPublicKey::Sender(SenderEphemeralPublicKey { r4: None, ..eph_pk });
    let bad_legs_verifier = vec![LegVerifierConfig {
        encryption: leg_enc_core,
        party_eph_pk: bad_eph_pk,
        has_balance_decreased: Some(true),
        has_counter_decreased: None,
    }];
    assert_err!(
        proof.verify(
            bad_legs_verifier,
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        ),
        Error::ProofVerificationError(_),
        "missing the asset-id ephemeral key"
    );
}

#[test]
fn affirmation_extra_amount_response_ignored() {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let enc_key_gen = account_comm_key.sk_enc_gen();

    let (((sk_aff, pk_aff), (sk_enc, pk_enc)), (_, (_, pk_r_e)), _) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let id = Fr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
    let leaf_blinding = Fr::rand(&mut rng);
    let re_randomized_account_commitment =
        (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();

    let rand_part_old_comm = Fr::rand(&mut rng);
    let rand_new_comm = Fr::rand(&mut rng);
    let nullifier = PallasA::rand(&mut rng);
    let nonce = b"test-nonce";

    let conf = LegEncConfig {
        parties_see_each_other: true,
        reveal_asset_id: false,
    };
    let (_, leg_enc, _) = setup_leg_with_conf(
        &mut rng,
        conf,
        pk_enc.0,
        None,
        amount,
        asset_id,
        pk_enc.0,
        pk_r_e.0,
        enc_key_gen,
        enc_gen,
    );
    let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();

    let k_asset_id = Fr::rand(&mut rng);
    // Hidden asset id, no balance change -> LegAuthLink::AssetIdOnly, partial_ct_amounts empty.
    let legs_prover = vec![LegProverConfig {
        encryption: leg_enc_core.clone(),
        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
        amount,
        has_balance_changed: false,
    }];

    let mut proof = AuthProofAffirmation::new(
        &mut rng,
        sk_aff.0,
        sk_enc.0,
        rand_part_old_comm,
        rand_new_comm,
        vec![],
        vec![k_asset_id],
        legs_prover,
        &re_randomized_account_commitment,
        &updated_account_comm.0,
        nullifier,
        nonce,
        account_comm_key.sk_gen(),
        enc_key_gen,
        b_blinding,
        enc_gen,
    )
    .unwrap();

    assert!(proof.partial_ct_amounts.is_empty());
    // Add an amount response the leg does not need; partial_ct_amounts stays empty.
    let resp_asset_id = proof.leg_links[0].resp_asset_id().unwrap().clone();
    let resp_amount = proof.resp_D.clone();
    proof.leg_links[0] = LegAuthLink::AssetIdAndAmount {
        resp_asset_id,
        resp_amount,
    };

    let legs_verifier = vec![LegVerifierConfig {
        encryption: leg_enc_core,
        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
        has_balance_decreased: None,
        has_counter_decreased: None,
    }];

    assert!(
        proof
            .verify(
                legs_verifier,
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            )
            .is_ok()
    );
}

#[test]
fn affirmation_leg_link_variant_matrix() {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 12;
    let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"testing");

    let asset_id = 1;
    let amount = 100;
    let enc_key_gen = account_comm_key.sk_enc_gen();

    let (((sk_aff, pk_aff), (sk_enc, pk_enc)), (_, (_, pk_r_e)), _) =
        setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

    let id = Fr::rand(&mut rng);
    let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
    account.balance = 200;
    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

    let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
    let leaf_blinding = Fr::rand(&mut rng);
    let re_rand = (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();
    let nonce = b"test-nonce";
    let nullifier = PallasA::rand(&mut rng);

    // Honest single-leg affirmation for the (reveal_asset_id, balance_changes) config.
    let build = |rng: &mut rand::rngs::ThreadRng, reveal: bool, balance: bool| {
        let (_, leg_enc, _) = setup_leg_with_conf(
            rng,
            LegEncConfig {
                parties_see_each_other: true,
                reveal_asset_id: reveal,
            },
            pk_enc.0,
            None,
            amount,
            asset_id,
            pk_enc.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );
        let (core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();
        let needs_amount = reveal || balance;
        let k_amounts = if needs_amount {
            vec![Fr::rand(rng)]
        } else {
            vec![]
        };
        let k_asset_ids = if reveal { vec![] } else { vec![Fr::rand(rng)] };
        let rand_part_old_comm = Fr::rand(rng);
        let rand_new_comm = Fr::rand(rng);
        let proof = AuthProofAffirmation::new(
            rng,
            sk_aff.0,
            sk_enc.0,
            rand_part_old_comm,
            rand_new_comm,
            k_amounts,
            k_asset_ids,
            vec![LegProverConfig {
                encryption: core.clone(),
                party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
                amount,
                has_balance_changed: balance,
            }],
            &re_rand,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
        )
        .unwrap();
        let verifier_leg = LegVerifierConfig {
            encryption: core,
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
            has_balance_decreased: if balance { Some(true) } else { None },
            has_counter_decreased: None,
        };
        (proof, verifier_leg)
    };

    let verify = |proof: &AuthProofAffirmation<PallasA>,
                  verifier_leg: &LegVerifierConfig<PallasA>| {
        proof.verify(
            vec![verifier_leg.clone()],
            &re_rand,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
            None,
        )
    };

    for reveal in [false, true] {
        for balance in [false, true] {
            let (proof, verifier_leg) = build(&mut rng, reveal, balance);
            let needs_amount = reveal || balance;
            let needs_asset_id = !reveal;

            assert!(
                verify(&proof, &verifier_leg).is_ok(),
                "honest reveal={reveal} balance={balance}"
            );

            let honest_amount = proof.leg_links[0].resp_amount().cloned();
            let honest_asset_id = proof.leg_links[0].resp_asset_id().cloned();
            let bogus_amount = proof.resp_D.clone();
            let bogus_asset_id = RespAssetId::Hidden(proof.resp_D.clone());

            if needs_amount {
                let mut p = proof.clone();
                p.leg_links[0] = LegAuthLink::AssetIdOnly {
                    resp_asset_id: bogus_asset_id.clone(),
                };
                assert!(
                    verify(&p, &verifier_leg).is_err(),
                    "dropped amount reveal={reveal} balance={balance}"
                );
            } else {
                let mut p = proof.clone();
                p.leg_links[0] = LegAuthLink::AssetIdAndAmount {
                    resp_asset_id: honest_asset_id.clone().unwrap(),
                    resp_amount: bogus_amount.clone(),
                };
                assert!(
                    verify(&p, &verifier_leg).is_ok(),
                    "extra amount reveal={reveal} balance={balance}"
                );
            }

            if needs_asset_id {
                let mut p = proof.clone();
                p.leg_links[0] = LegAuthLink::AmountOnly {
                    resp_amount: bogus_amount.clone(),
                };
                assert!(
                    verify(&p, &verifier_leg).is_err(),
                    "dropped asset-id reveal={reveal} balance={balance}"
                );
            } else {
                let mut p = proof.clone();
                p.leg_links[0] = LegAuthLink::AssetIdAndAmount {
                    resp_asset_id: bogus_asset_id.clone(),
                    resp_amount: honest_amount.clone().unwrap(),
                };
                assert!(
                    verify(&p, &verifier_leg).is_ok(),
                    "extra asset-id reveal={reveal} balance={balance}"
                );
            }
        }
    }
}

#[test]
fn affirm_other_account_encryption_key() {
    // Standalone affirmation auth accepts this proof even when the consumed account key differs
    // from the leg key. The split verifier is the layer that checks the account leaf against the
    // proof's partial commitment.
    let mut rng = thread_rng();
    // Use independent bases so the mismatch is not hidden by setup.
    let sk_gen = Affine::<PallasConfig>::rand(&mut rng);
    let enc_key_gen = Affine::<PallasConfig>::rand(&mut rng);
    let comm_re_rand_gen = Affine::<PallasConfig>::rand(&mut rng);
    let enc_gen = Affine::<PallasConfig>::rand(&mut rng);

    let sk_e = Fr::rand(&mut rng);
    let sk_enc_e = Fr::rand(&mut rng);
    // Use a different encryption key for the leg sender.
    let (sk_enc_a_keys, ek_a) = keygen_enc(&mut rng, enc_key_gen);
    let sk_enc_a = sk_enc_a_keys.0;

    let amount = 100u64;
    let asset_id = 7u32;
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
    let leg = Leg::new(ek_a.0, pk_r_e.0, amount, asset_id, vec![], vec![], vec![]).unwrap();
    let cfg = LegEncConfig {
        parties_see_each_other: false,
        reveal_asset_id: false,
    };
    let (leg_enc, _) = leg.encrypt(&mut rng, cfg, enc_key_gen, enc_gen).unwrap();
    let (leg_core, eph_pk_s) = leg_enc.core_and_eph_keys_for_sender();

    // The account leaf commits sk_enc_e, while the proof below is built with sk_enc_a.
    let rand_old = Fr::rand(&mut rng);
    let rand_new = Fr::rand(&mut rng);
    let pk_e = (sk_gen * sk_e + enc_key_gen * sk_enc_e).into_affine();
    let re_rand_leaf = (pk_e + comm_re_rand_gen * rand_old).into_affine();
    let updated_comm = (pk_e + comm_re_rand_gen * rand_new).into_affine();
    let nullifier = Affine::<PallasConfig>::rand(&mut rng);
    let nonce = b"acA1_split_gap";
    let k_amount = Fr::rand(&mut rng);
    let k_asset_id = Fr::rand(&mut rng);

    let legs = vec![LegProverConfig {
        encryption: leg_core.clone(),
        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s.clone()),
        amount,
        has_balance_changed: true,
    }];
    let proof = AuthProofAffirmation::<Affine<PallasConfig>>::new(
        &mut rng,
        sk_e,
        sk_enc_a,
        rand_old,
        rand_new,
        vec![k_amount],
        vec![k_asset_id],
        legs,
        &re_rand_leaf,
        &updated_comm,
        nullifier,
        nonce,
        sk_gen,
        enc_key_gen,
        comm_re_rand_gen,
        enc_gen,
    )
    .unwrap();

    let conf = vec![LegVerifierConfig {
        encryption: leg_core,
        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s),
        has_balance_decreased: Some(true),
        has_counter_decreased: Some(false),
    }];
    proof
        .verify(
            conf,
            &re_rand_leaf,
            &updated_comm,
            nullifier,
            nonce,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            enc_gen,
            None,
        )
        .unwrap();
}
