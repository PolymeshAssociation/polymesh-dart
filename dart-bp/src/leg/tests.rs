#![allow(deprecated)]

use super::*;
use crate::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc, keygen_sig};
use crate::leg::leg_proof::LegCreationProof;
use crate::leg::public_asset_leg_proof::PublicAssetLegCreationProof;
use crate::leg::settlement_proof::SettlementCreationProof;
use crate::util::{
    add_verification_tuples_batches_to_rmc, batch_verify_bp, get_verification_tuples_with_rng,
    prove_with_rng, verify_rmc, verify_with_rng,
};
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_pallas::{Affine as PallasA, Fr as PallasScalar, PallasConfig};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_vesta::{Fr as VestaScalar, VestaConfig};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use bulletproofs::r1cs::{Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::curve_tree::CurveTree;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use proptest::prelude::*;
use std::time::Instant;

type PallasParameters = PallasConfig;
type VestaParameters = VestaConfig;

/// Generate account signing and encryption keys for all sender, receiver, and auditor.
/// This is just for testing and in practice, each party generates its own keys.
pub fn setup_keys<R: CryptoRngCore, G: AffineRepr>(
    rng: &mut R,
    sig_key_gen: G,
    enc_key_gen: G,
) -> (
    ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
    ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
    ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
) {
    // Account signing (affirmation) keys
    let (sk_s, pk_s) = keygen_sig(rng, sig_key_gen);
    let (sk_r, pk_r) = keygen_sig(rng, sig_key_gen);
    let (sk_a, pk_a) = keygen_sig(rng, sig_key_gen);

    // Encryption keys
    let (sk_s_e, pk_s_e) = keygen_enc(rng, enc_key_gen);
    let (sk_r_e, pk_r_e) = keygen_enc(rng, enc_key_gen);
    let (sk_a_e, pk_a_e) = keygen_enc(rng, enc_key_gen);
    (
        ((sk_s, pk_s), (sk_s_e, pk_s_e)),
        ((sk_r, pk_r), (sk_r_e, pk_r_e)),
        ((sk_a, pk_a), (sk_a_e, pk_a_e)),
    )
}

#[test]
fn leg_encryption_configs() {
    let mut rng = rand::thread_rng();

    let label = b"enc-config-test";
    let sig_key_gen = hash_to_pallas(label, b"sig-key-g").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let (sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

    let keys_enc = (0..2)
        .map(|_| keygen_enc(&mut rng, enc_key_gen))
        .collect::<Vec<_>>();
    let keys_mediator = (0..2)
        .map(|_| keygen_sig(&mut rng, sig_key_gen))
        .collect::<Vec<_>>();
    let keys_public_enc = (0..2)
        .map(|_| keygen_enc(&mut rng, enc_key_gen))
        .collect::<Vec<_>>();

    let amount = 100;
    let asset_id = 1;

    let enc_keys = keys_enc.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
    let med_keys = keys_mediator.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
    let public_enc_keys = keys_public_enc.iter().map(|(_, k)| k.0).collect::<Vec<_>>();

    let leg = Leg::new(
        pk_s_e.0,
        pk_r_e.0,
        amount,
        asset_id,
        enc_keys.clone(),
        med_keys.clone(),
        public_enc_keys.clone(),
    )
    .unwrap();

    let (leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegEncConfig {
                visibility: PartyVisibility::FullVisibility,
                reveal_asset_id: true,
            },
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

    assert!(leg_enc.is_asset_id_revealed());
    assert_eq!(leg_enc.asset_id(), Some(asset_id));
    assert_eq!(leg_enc.asset_id_ciphertext(), None);

    let (s_pk, r_pk_opt, a_id, amt) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
    assert_eq!(s_pk, pk_s_e.0);
    assert_eq!(r_pk_opt, Some(pk_r_e.0));
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    let (s_pk_opt, r_pk, a_id, amt) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
    assert_eq!(s_pk_opt, Some(pk_s_e.0));
    assert_eq!(r_pk, pk_r_e.0);
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    for (i, (sk_enc, _)) in keys_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, false, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }

    for (i, (sk_enc, _)) in keys_public_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, true, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }

    let (leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegEncConfig {
                visibility: PartyVisibility::NoVisibility,
                reveal_asset_id: false,
            },
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

    assert!(!leg_enc.is_asset_id_revealed());
    assert!(leg_enc.asset_id_ciphertext().is_some());
    assert_eq!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r2, None);
    assert_eq!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r1, None);
    assert_eq!(
        leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r4.is_some(),
        true
    );
    assert_eq!(
        leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r4.is_some(),
        true
    );

    let (s_pk, r_pk_opt, a_id, amt) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
    assert_eq!(s_pk, pk_s_e.0);
    assert_eq!(r_pk_opt, None);
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    let (s_pk_opt, r_pk, a_id, amt) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
    assert_eq!(s_pk_opt, None);
    assert_eq!(r_pk, pk_r_e.0);
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    for (i, (sk_enc, _)) in keys_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, false, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }

    for (i, (sk_enc, _)) in keys_public_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, true, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }

    let (leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegEncConfig {
                visibility: PartyVisibility::OnlySenderSeesReceiver,
                reveal_asset_id: false,
            },
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

    assert!(!leg_enc.is_asset_id_revealed());
    assert!(leg_enc.asset_id_ciphertext().is_some());
    assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r2.is_some());
    assert_eq!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r1, None);
    assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r4.is_some());
    assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r4.is_some());

    let (s_pk, r_pk_opt, a_id, amt) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
    assert_eq!(s_pk, pk_s_e.0);
    assert_eq!(r_pk_opt, Some(pk_r_e.0));
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    let (s_pk_opt, r_pk, a_id, amt) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
    assert_eq!(s_pk_opt, None);
    assert_eq!(r_pk, pk_r_e.0);
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    for (i, (sk_enc, _)) in keys_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, false, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }

    for (i, (sk_enc, _)) in keys_public_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, true, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }

    let (leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegEncConfig {
                visibility: PartyVisibility::OnlyReceiverSeesSender,
                reveal_asset_id: true,
            },
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

    assert!(leg_enc.is_asset_id_revealed());
    assert_eq!(leg_enc.asset_id(), Some(asset_id));
    assert_eq!(leg_enc.asset_id_ciphertext(), None);
    assert_eq!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r2, None);
    assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r1.is_some());

    let (s_pk, r_pk_opt, a_id, amt) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
    assert_eq!(s_pk, pk_s_e.0);
    assert_eq!(r_pk_opt, None);
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    let (s_pk_opt, r_pk, a_id, amt) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
    assert_eq!(s_pk_opt, Some(pk_s_e.0));
    assert_eq!(r_pk, pk_r_e.0);
    assert_eq!(a_id, asset_id);
    assert_eq!(amt, amount);

    for (i, (sk_enc, _)) in keys_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, false, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }

    for (i, (sk_enc, _)) in keys_public_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, true, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, asset_id);
        assert_eq!(amt, amount);
    }
}

#[test]
fn leg_verification() {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;

    let label = b"asset-tree-params";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let asset_id = 1;
    let amount = 100;
    let nonce = b"test-nonce";

    let (sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

    let mut test_with_config = |visibility: PartyVisibility,
                                num_enc_keys: u8,
                                num_mediators: u8,
                                num_public_enc_keys: u8,
                                num_public_mediators: u8| {
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_enc_keys as u32,
            num_mediators as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let keys_enc = (0..num_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();
        let keys_public_enc = (0..num_public_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let enc_secrets = keys_enc.iter().map(|(sk, _)| sk.0).collect::<Vec<_>>();
        let keys_enc = keys_enc.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        // Mediator affirmation keys
        let keys_mediator = keys_mediator.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        let public_enc_keys: Vec<_> = keys_public_enc.iter().map(|(_, k)| k.0).collect();

        let asset_data = AssetData::new(
            asset_id,
            keys_enc.clone(),
            keys_mediator.clone(),
            &asset_comm_params,
        )
        .unwrap();

        let set = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set,
            &asset_tree_params,
            Some(4),
        );

        let clock = Instant::now();

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            keys_enc.clone(),
            keys_mediator.clone(),
            public_enc_keys.clone(),
        )
        .unwrap();

        let config = LegEncConfig {
            visibility,
            reveal_asset_id: false, // asset-id is always hidden
        };

        let (leg_enc, leg_enc_rand) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = asset_tree.root_node();

        let proof =
            LegCreationProof::<L, PallasScalar, VestaScalar, PallasConfig, VestaParameters>::new::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                leg.clone(),
                leg_enc.clone(),
                leg_enc_rand.clone(),
                path,
                asset_data.clone(),
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                leg_enc.clone(),
                &root,
                public_enc_keys.clone(),
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time_regular = clock.elapsed();

        let clock = Instant::now();
        let mut rmc_1 = RandomizedMultChecker::new(ark_vesta::Fr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
        proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                leg_enc.clone(),
                &root,
                public_enc_keys.clone(),
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();

        verify_rmc(rmc_0, rmc_1).unwrap();
        let verifier_time_rmc = clock.elapsed();

        let (p1, p2, a, b) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
        assert_eq!(p1, pk_s_e.0);
        if visibility.sender_sees_receiver() {
            assert_eq!(p2.unwrap(), pk_r_e.0);
        } else {
            assert!(p2.is_none());
        }
        assert_eq!(a, asset_id);
        assert_eq!(b, amount);

        let (p1, p2, a, b) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
        if visibility.receiver_sees_sender() {
            assert_eq!(p1.unwrap(), pk_s_e.0);
        } else {
            assert!(p1.is_none());
        }
        assert_eq!(p2, pk_r_e.0);
        assert_eq!(a, asset_id);
        assert_eq!(b, amount);

        for (i, sk_enc) in enc_secrets.iter().enumerate() {
            let (s, r, a, b) = leg_enc
                .decrypt_given_key(sk_enc, false, i, enc_gen)
                .unwrap();
            assert_eq!(s, pk_s_e.0);
            assert_eq!(r, pk_r_e.0);
            assert_eq!(a, asset_id);
            assert_eq!(b, amount);
        }

        for (j, med) in leg_enc.mediators.iter().flatten().enumerate() {
            // Each entry is encrypted to every asset encryption key, so any of them recovers it.
            for (k, sk_enc) in enc_secrets.iter().enumerate() {
                let recovered_mk = med.affirmation_key(sk_enc, k).unwrap();
                assert_eq!(recovered_mk, keys_mediator[j]);
            }
        }

        println!(
            "visibility={:?}, num_enc_keys={}, num_mediators={}, num_public_enc_keys={}, num_public_mediators={}, L={L}, height={}",
            visibility,
            num_enc_keys,
            num_mediators,
            num_public_enc_keys,
            num_public_mediators,
            asset_tree.height()
        );
        println!(
            "total proof size = {}",
            proof.compressed_size() + leg_enc.compressed_size()
        );
        println!("total prover time = {:?}", prover_time);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular, verifier_time_rmc
        );
    };

    test_with_config(PartyVisibility::FullVisibility, 2, 2, 1, 1);
    test_with_config(PartyVisibility::NoVisibility, 2, 2, 1, 1);
    test_with_config(PartyVisibility::OnlySenderSeesReceiver, 2, 2, 1, 1);
    test_with_config(PartyVisibility::OnlyReceiverSeesSender, 2, 2, 1, 1);

    test_with_config(PartyVisibility::FullVisibility, 0, 0, 0, 0);
    test_with_config(PartyVisibility::NoVisibility, 0, 0, 0, 0);
    test_with_config(PartyVisibility::OnlySenderSeesReceiver, 0, 0, 0, 0);
    test_with_config(PartyVisibility::OnlyReceiverSeesSender, 0, 0, 0, 0);

    test_with_config(PartyVisibility::FullVisibility, 0, 0, 1, 1);
    test_with_config(PartyVisibility::NoVisibility, 0, 0, 1, 1);
    test_with_config(PartyVisibility::OnlySenderSeesReceiver, 0, 0, 1, 1);
    test_with_config(PartyVisibility::OnlyReceiverSeesSender, 0, 0, 1, 1);
}

#[test]
fn batch_leg_verification() {
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;

    let label = b"asset-tree-params";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let batch_size = 5;

    // Encryption keys
    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

    let mut test_with_config = |parties_see_each_other: bool,
                                num_auditors: u8,
                                num_mediators: u8| {
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors as u32,
            num_mediators as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let keys_auditor = keys_auditor.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        // Mediator affirmation keys
        let keys_mediator = keys_mediator.iter().map(|(_, k)| k.0).collect::<Vec<_>>();

        let mut asset_data_vec = Vec::with_capacity(batch_size);
        let mut commitments = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let asset_data = AssetData::new(
                asset_id,
                keys_auditor.clone(),
                keys_mediator.clone(),
                &asset_comm_params,
            )
            .unwrap();

            commitments.push(asset_data.commitment);
            asset_data_vec.push(asset_data);
        }

        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(4),
        );
        let root = asset_tree.root_node();

        let config = LegEncConfig {
            visibility: if parties_see_each_other {
                PartyVisibility::FullVisibility
            } else {
                PartyVisibility::NoVisibility
            },
            reveal_asset_id: false,
        };

        let mut proofs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut nonces = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let nonce = format!("nonce_{}", i).into_bytes();
            let amount = (i + 100) as u64;
            let asset_id = (i + 1) as u32;

            let leg = Leg::new(
                pk_s_e.0,
                pk_r_e.0,
                amount,
                asset_id,
                keys_auditor.clone(),
                keys_mediator.clone(),
                vec![],
            )
            .unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt(&mut rng, config.clone(), enc_key_gen, enc_gen)
                .unwrap();

            let path = asset_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

            let proof = LegCreationProof::<
                L,
                PallasScalar,
                VestaScalar,
                PallasConfig,
                VestaParameters,
            >::new::<_, PallasParams, VestaParams>(
                &mut rng,
                leg,
                leg_enc.clone(),
                leg_enc_rand,
                path,
                asset_data_vec[i].clone(),
                &root,
                &nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            proofs.push(proof);
            leg_encs.push(leg_enc);
            nonces.push(nonce);
        }

        let clock = Instant::now();

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            proofs[i]
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    leg_encs[i].clone(),
                    &root,
                    vec![],
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
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
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    leg_encs[i].clone(),
                    &root,
                    vec![],
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
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
            asset_tree_params.even_parameters.pc_gens(),
            asset_tree_params.odd_parameters.pc_gens(),
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
        )
        .unwrap();

        let batch_verifier_time = clock.elapsed();

        println!(
            "parties_see_each_other={}, num_auditors={}, num_mediators={}, L={L}, height={}",
            parties_see_each_other,
            num_auditors,
            num_mediators,
            asset_tree.height()
        );
        println!(
            "For {batch_size} leg verification proofs, verifier time = {:?}, batch verifier time {:?}",
            verifier_time, batch_verifier_time
        );

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    leg_encs[i].clone(),
                    &root,
                    vec![],
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
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
        verify_rmc(rmc_0, rmc_1).unwrap();
        let batch_verifier_rmc_time = clock.elapsed();

        println!(
            "For {batch_size} leg verification proofs, batch_verifier_rmc_time time {:?}",
            batch_verifier_rmc_time
        );
    };

    test_with_config(true, 2, 2);

    test_with_config(false, 2, 2);

    test_with_config(true, 1, 1);
}

#[test]
fn combined_leg_verification() {
    // Unlike batch_* (independent proofs, only the final mult-check batched), all leg proofs here share one
    // prover/transcript and aggregate into a single R1CS/Bulletproof, verified via verify_with_rng (+ an RMC pass).
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 16;
    const L: usize = 64;

    let height = 4;
    let batch_size = 5;
    let amount = 100;

    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

    let mut test_with_config =
        |parties_see_each_other: bool, num_auditors: u8, num_mediators: u8| {
            let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
                b"asset-comm-params",
                num_auditors as u32,
                num_mediators as u32,
                &asset_tree_params.even_parameters.bp_gens(),
            );

            let keys_auditor = (0..num_auditors)
                .map(|_| keygen_enc(&mut rng, enc_key_gen))
                .collect::<Vec<_>>();
            let keys_mediator = (0..num_mediators)
                .map(|_| keygen_sig(&mut rng, sig_key_gen))
                .collect::<Vec<_>>();

            let keys_auditor = keys_auditor.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
            // Mediator affirmation keys
            let keys_mediator = keys_mediator.iter().map(|(_, k)| k.0).collect::<Vec<_>>();

            let mut asset_data_vec = Vec::with_capacity(batch_size);
            let mut commitments = Vec::with_capacity(batch_size);
            for i in 0..batch_size {
                let asset_id = (i + 1) as u32;
                let asset_data = AssetData::new(
                    asset_id,
                    keys_auditor.clone(),
                    keys_mediator.clone(),
                    &asset_comm_params,
                )
                .unwrap();
                commitments.push(asset_data.commitment);
                asset_data_vec.push(asset_data);
            }

            let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
                &commitments,
                &asset_tree_params,
                Some(height),
            );
            let root = asset_tree.root_node();

            let config = LegEncConfig {
                visibility: if parties_see_each_other {
                    PartyVisibility::FullVisibility
                } else {
                    PartyVisibility::NoVisibility
                },
                reveal_asset_id: false,
            };

            let mut legs = Vec::with_capacity(batch_size);
            let mut leg_encs = Vec::with_capacity(batch_size);
            let mut leg_enc_rands = Vec::with_capacity(batch_size);
            let mut nonces = Vec::with_capacity(batch_size);

            for i in 0..batch_size {
                let asset_id = (i + 1) as u32;
                let leg = Leg::new(
                    pk_s_e.0,
                    pk_r_e.0,
                    amount,
                    asset_id,
                    keys_auditor.clone(),
                    keys_mediator.clone(),
                    vec![],
                )
                .unwrap();
                let (leg_enc, leg_enc_rand) = leg
                    .encrypt(&mut rng, config.clone(), enc_key_gen, enc_gen)
                    .unwrap();

                legs.push(leg);
                leg_encs.push(leg_enc);
                leg_enc_rands.push(leg_enc_rand);
                nonces.push(format!("nonce_{}", i).into_bytes());
            }

            let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
            let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
            let mut even_prover = Prover::new(
                &asset_tree_params.even_parameters.pc_gens(),
                even_transcript,
            );
            let mut odd_prover =
                Prover::new(&asset_tree_params.odd_parameters.pc_gens(), odd_transcript);

            let mut proofs = Vec::with_capacity(batch_size);
            let clock = Instant::now();

            for i in 0..batch_size {
                let path = asset_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

                let proof = LegCreationProof::<
                    L,
                    PallasScalar,
                    VestaScalar,
                    PallasConfig,
                    VestaParameters,
                >::new_with_given_prover::<_, PallasParams, VestaParams>(
                    &mut rng,
                    legs[i].clone(),
                    leg_encs[i].clone(),
                    leg_enc_rands[i].clone(),
                    path,
                    asset_data_vec[i].clone(),
                    &root,
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut even_prover,
                    &mut odd_prover,
                )
                .unwrap();
                proofs.push(proof);
            }

            let (even_bp, odd_bp) = prove_with_rng(
                even_prover,
                odd_prover,
                &asset_tree_params.even_parameters.bp_gens(),
                &asset_tree_params.odd_parameters.bp_gens(),
                &mut rng,
            )
            .unwrap();
            let prover_time = clock.elapsed();

            let clock = Instant::now();
            let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
            let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
            let mut even_verifier = Verifier::new(even_transcript);
            let mut odd_verifier = Verifier::new(odd_transcript);

            for i in 0..batch_size {
                proofs[i]
                    .verify_sigma_protocols_and_enforce_constraints(
                        leg_encs[i].clone(),
                        &root,
                        vec![],
                        &nonces[i],
                        &asset_tree_params,
                        &asset_comm_params,
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
                asset_tree_params.even_parameters.pc_gens(),
                asset_tree_params.odd_parameters.pc_gens(),
                asset_tree_params.even_parameters.bp_gens(),
                asset_tree_params.odd_parameters.bp_gens(),
                &mut rng,
            )
            .unwrap();

            let verification_time = clock.elapsed();

            let clock = Instant::now();
            let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
            let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
            let mut even_verifier = Verifier::new(transcript_even);
            let mut odd_verifier = Verifier::new(transcript_odd);
            let mut rmc_0 = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
            let mut rmc_1 = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));

            let root = asset_tree.root_node();
            for i in 0..batch_size {
                proofs[i]
                    .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                        leg_encs[i].clone(),
                        &root,
                        vec![],
                        &nonces[i],
                        &asset_tree_params,
                        &asset_comm_params,
                        enc_key_gen,
                        enc_gen,
                        &mut even_verifier,
                        &mut odd_verifier,
                        Some(&mut rmc_1),
                    )
                    .unwrap();
            }

            let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
                even_verifier,
                odd_verifier,
                &even_bp,
                &odd_bp,
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
                &mut rmc_0,
                &mut rmc_1,
            )
            .unwrap();
            verify_rmc(rmc_0, rmc_1).unwrap();
            let rmc_verification_time = clock.elapsed();

            println!(
                "parties_see_each_other={}, num_auditors={}, num_mediators={}, L={L}, height={}",
                parties_see_each_other,
                num_auditors,
                num_mediators,
                asset_tree.height()
            );
            println!("Combined leg proving time = {:?}", prover_time);
            println!("Combined leg verification time = {:?}", verification_time);
            println!(
                "Combined leg RMC verification time = {:?}",
                rmc_verification_time
            );
            println!(
                "Combined proof size = {} bytes",
                even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
            );
        };

    test_with_config(true, 2, 3);
    test_with_config(false, 2, 3);
    test_with_config(true, 1, 1);
}

#[test]
fn settlement_verification() {
    // Single settlement proof over a growing leg count (2-, then 4-, then 5-leg bundles), run for both
    // reveal_asset_id=false (legs need curve-tree membership) and =true (asset ids public); regular + RMC verify.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 14;
    const L: usize = 64;
    const M: usize = 2;

    let height = 6;

    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        0,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let asset_id_1 = 1;
    let asset_id_2 = 2;
    let asset_id_3 = 3;
    let asset_id_4 = 4;
    let asset_id_5 = 5;

    // Setup keys for 2 pairs of sender/receiver
    let (_, pk_s_e1) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e1) = keygen_enc(&mut rng, enc_key_gen);

    let (_, pk_s_e2) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e2) = keygen_enc(&mut rng, enc_key_gen);

    // Auditor key
    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);

    let enc_keys = vec![pk_a_e.0];
    let med_keys = vec![];
    // Create 5 asset data entries with different asset IDs
    let mut asset_data = Vec::new();
    let mut commitments = Vec::new();
    for i in 0..5 {
        let asset_id = (i + 1) as u32;
        let ad = AssetData::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
        )
        .unwrap();
        commitments.push(ad.commitment);
        asset_data.push(ad);
    }

    // Create the asset tree with all asset data
    let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
        &commitments,
        &asset_tree_params,
        Some(height),
    );

    let root = asset_tree.root_node();
    let amount = 100;
    let nonce = b"test-nonce";

    let mut test_with_config = |reveal_asset_id: bool| {
        // Create 2 legs
        let leg_1 = Leg::new(
            pk_s_e1.0,
            pk_r_e1.0,
            amount,
            asset_id_1,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let leg_2 = Leg::new(
            pk_s_e2.0,
            pk_r_e2.0,
            amount,
            asset_id_2,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();

        let (leg_enc1, leg_enc_rand1) = leg_1
            .encrypt(
                &mut rng,
                LegEncConfig {
                    reveal_asset_id,
                    visibility: PartyVisibility::FullVisibility,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let (leg_enc2, leg_enc_rand2) = leg_2
            .encrypt(
                &mut rng,
                LegEncConfig {
                    reveal_asset_id,
                    visibility: PartyVisibility::FullVisibility,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let path_1 = asset_tree.get_paths_to_leaves(&[0, 1]).unwrap();

        println!("For tree with height {height}, L={L}, M={M}, reveal_asset_id={reveal_asset_id}");

        println!("For 2 leg settlement");

        let (leaf_paths, asset_data_vec) = if !reveal_asset_id {
            (
                vec![path_1.clone()],
                vec![asset_data[0].clone(), asset_data[1].clone()],
            )
        } else {
            (vec![], vec![])
        };
        let clock = Instant::now();
        let proof =
            SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![leg_1.clone(), leg_2.clone()],
                vec![leg_enc1.clone(), leg_enc2.clone()],
                vec![leg_enc_rand1.clone(), leg_enc_rand2.clone()],
                leaf_paths,
                asset_data_vec,
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time = clock.elapsed();

        let enc_keys = if !reveal_asset_id {
            vec![]
        } else {
            // When asset IDs are revealed, provide encryption keys for verification
            // enc_keys: one Vec<Affine> per revealed asset leg
            vec![vec![pk_a_e.0], vec![pk_a_e.0]]
        };

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                vec![leg_enc1.clone(), leg_enc2.clone()],
                &root,
                enc_keys.clone(),
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifying_time = clock.elapsed();

        let clock = Instant::now();
        let mut rmc_1 = RandomizedMultChecker::new(ark_vesta::Fr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
        proof
            .verify(
                &mut rng,
                vec![leg_enc1.clone(), leg_enc2.clone()],
                &root,
                enc_keys,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let verifying_time_rmc = clock.elapsed();

        println!(
            "Proving time: {:?}, verifying time: {:?}, verifier time (RandomizedMultChecker) = {:?}, proof size {}",
            proving_time,
            verifying_time,
            verifying_time_rmc,
            proof.compressed_size()
        );

        // Create 2 more legs
        let leg_3 = Leg::new(
            pk_s_e1.0,
            pk_r_e1.0,
            amount,
            asset_id_3,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let leg_4 = Leg::new(
            pk_s_e2.0,
            pk_r_e2.0,
            amount,
            asset_id_4,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();

        let (leg_enc3, leg_enc_rand3) = leg_3
            .encrypt(
                &mut rng,
                LegEncConfig {
                    reveal_asset_id,
                    visibility: PartyVisibility::FullVisibility,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let (leg_enc4, leg_enc_rand4) = leg_4
            .encrypt(
                &mut rng,
                LegEncConfig {
                    reveal_asset_id,
                    visibility: PartyVisibility::FullVisibility,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let path_2 = asset_tree.get_paths_to_leaves(&[2, 3]).unwrap();

        println!("For 4 leg settlement");

        let (leaf_paths, asset_data_vec) = if !reveal_asset_id {
            (
                vec![path_1.clone(), path_2.clone()],
                vec![
                    asset_data[0].clone(),
                    asset_data[1].clone(),
                    asset_data[2].clone(),
                    asset_data[3].clone(),
                ],
            )
        } else {
            (vec![], vec![])
        };

        let clock = Instant::now();
        let proof =
            SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![leg_1.clone(), leg_2.clone(), leg_3.clone(), leg_4.clone()],
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                ],
                vec![
                    leg_enc_rand1.clone(),
                    leg_enc_rand2.clone(),
                    leg_enc_rand3.clone(),
                    leg_enc_rand4.clone(),
                ],
                leaf_paths,
                asset_data_vec,
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time = clock.elapsed();

        let enc_keys = if !reveal_asset_id {
            vec![]
        } else {
            vec![
                vec![pk_a_e.0],
                vec![pk_a_e.0],
                vec![pk_a_e.0],
                vec![pk_a_e.0],
            ]
        };

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                ],
                &root,
                enc_keys.clone(),
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifying_time = clock.elapsed();

        let clock = Instant::now();
        let mut rmc_1 = RandomizedMultChecker::new(ark_vesta::Fr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
        proof
            .verify(
                &mut rng,
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                ],
                &root,
                enc_keys,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let verifying_time_rmc = clock.elapsed();

        println!(
            "Proving time: {:?}, verifying time: {:?}, verifier time (RandomizedMultChecker) = {:?}, proof size {}",
            proving_time,
            verifying_time,
            verifying_time_rmc,
            proof.compressed_size()
        );

        // Create 1 more leg
        let leg_5 = Leg::new(
            pk_s_e1.0,
            pk_r_e1.0,
            amount,
            asset_id_5,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc5, leg_enc_rand5) = leg_5
            .encrypt(
                &mut rng,
                LegEncConfig {
                    reveal_asset_id,
                    visibility: PartyVisibility::FullVisibility,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let path_3 = asset_tree.get_paths_to_leaves(&[4]).unwrap();

        println!("For 5 leg settlement");

        let (leaf_paths, asset_data_vec) = if !reveal_asset_id {
            (
                vec![path_1.clone(), path_2.clone(), path_3.clone()],
                vec![
                    asset_data[0].clone(),
                    asset_data[1].clone(),
                    asset_data[2].clone(),
                    asset_data[3].clone(),
                    asset_data[4].clone(),
                ],
            )
        } else {
            (vec![], vec![])
        };

        let clock = Instant::now();
        let proof =
            SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![
                    leg_1.clone(),
                    leg_2.clone(),
                    leg_3.clone(),
                    leg_4.clone(),
                    leg_5.clone(),
                ],
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                    leg_enc5.clone(),
                ],
                vec![
                    leg_enc_rand1.clone(),
                    leg_enc_rand2.clone(),
                    leg_enc_rand3.clone(),
                    leg_enc_rand4.clone(),
                    leg_enc_rand5.clone(),
                ],
                leaf_paths,
                asset_data_vec,
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time = clock.elapsed();

        let enc_keys = if !reveal_asset_id {
            vec![]
        } else {
            vec![
                vec![pk_a_e.0],
                vec![pk_a_e.0],
                vec![pk_a_e.0],
                vec![pk_a_e.0],
                vec![pk_a_e.0],
            ]
        };

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                    leg_enc5.clone(),
                ],
                &root,
                enc_keys.clone(),
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifying_time = clock.elapsed();

        let clock = Instant::now();
        let mut rmc_1 = RandomizedMultChecker::new(ark_vesta::Fr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
        proof
            .verify(
                &mut rng,
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                    leg_enc5.clone(),
                ],
                &root,
                enc_keys,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let verifying_time_rmc = clock.elapsed();

        println!(
            "Proving time: {:?}, verifying time: {:?}, verifier time (RandomizedMultChecker) = {:?}, proof size {}",
            proving_time,
            verifying_time,
            verifying_time_rmc,
            proof.compressed_size()
        );
    };

    test_with_config(false);

    test_with_config(true);
}

#[test]
fn batch_settlement_verification() {
    // 5 INDEPENDENT settlement proofs (each with a different leg count: M-1, M, M+1 legs), verified together
    // by batching only the final BP/mult-checks (batch_verify_bp + RMC) — vs combined_* which shares one prover.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 15;
    const L: usize = 64;
    const M: usize = 2;

    let height = 4;

    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        0,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let mut all_asset_data = Vec::new();
    let mut commitments = Vec::new();
    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
    let enc_keys = vec![pk_a_e.0];
    let med_keys = vec![];

    for i in 0..(M + 1) {
        let asset_id = (i + 1) as u32;
        let ad = AssetData::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
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
    let root = asset_tree.root_node();

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
    let amount = 100;

    let batch_size = 5;
    let mut nonces = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        nonces.push(format!("nonce_{}", i).into_bytes());
    }

    let mut proofs = Vec::with_capacity(batch_size);
    let mut all_leg_encs = Vec::with_capacity(batch_size);

    for i in 0..batch_size {
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

        for j in 0..num_legs {
            // Reuse all_asset_data in loop (wrap around logic if num_legs > all_asset_data.len(), but here num_legs <= M+1 so OK)
            let ad_idx = j % all_asset_data.len();
            let leg = Leg::new(
                pk_s_e.0,
                pk_r_e.0,
                amount,
                all_asset_data[ad_idx].id,
                vec![pk_a_e.0],
                vec![],
                vec![],
            )
            .unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                .unwrap();

            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
            asset_data.push(all_asset_data[ad_idx].clone());
        }

        for chunk in (0..num_legs as u32).collect::<Vec<_>>().chunks(M) {
            let path = asset_tree.get_paths_to_leaves(chunk).unwrap();
            leaf_paths.push(path);
        }

        let proof =
            SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
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

    let clock = Instant::now();
    for i in 0..batch_size {
        proofs[i]
            .verify(
                &mut rng,
                all_leg_encs[i].clone(),
                &root,
                vec![],
                vec![],
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
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

    for i in 0..batch_size {
        let (even, odd) = proofs[i]
            .verify_and_return_tuples(
                all_leg_encs[i].clone(),
                &root,
                vec![],
                vec![],
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();
        even_tuples.push(even);
        odd_tuples.push(odd);
    }
    let batch_tuple_time = clock.elapsed();

    let clock = Instant::now();
    batch_verify_bp(
        even_tuples,
        odd_tuples,
        asset_tree_params.even_parameters.pc_gens(),
        asset_tree_params.odd_parameters.pc_gens(),
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
    )
    .unwrap();
    let batch_bp_time = clock.elapsed();

    let clock = Instant::now();
    let mut even_tuples = Vec::with_capacity(batch_size);
    let mut odd_tuples = Vec::with_capacity(batch_size);
    let mut rmc_0 = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));

    for i in 0..batch_size {
        let (even, odd) = proofs[i]
            .verify_and_return_tuples(
                all_leg_encs[i].clone(),
                &root,
                vec![],
                vec![],
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut rng,
                Some(&mut rmc_1),
            )
            .unwrap();
        even_tuples.push(even);
        odd_tuples.push(odd);
    }

    let batch_tuple_rmc_time = clock.elapsed();

    let clock = Instant::now();
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
    let rmc_time = clock.elapsed();

    println!(
        "Verifier time = {:?}, batch tuple time {:?}, batch BP time {:?}, batch_tuple_rmc_time {:?}, batch_verifier_rmc_time {:?}",
        verifier_time, batch_tuple_time, batch_bp_time, batch_tuple_rmc_time, rmc_time
    );
}

#[test]
fn large_settlement_verification() {
    // Size stress: ONE settlement proof bundling 20 legs (all the same hidden-asset id, M=8 so multiple
    // membership chunks), verified with the RMC path — checks a single big settlement still proves/verifies.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;
    const M: usize = 8;

    let height = 4;

    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        0,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
    let enc_keys = vec![pk_a_e.0];
    let med_keys = vec![];

    // Create single asset data
    let asset_id = 1;
    let asset_data = AssetData::new(
        asset_id,
        enc_keys.clone(),
        med_keys.clone(),
        &asset_comm_params,
    )
    .unwrap();

    let commitments = vec![asset_data.commitment];

    let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
        &commitments,
        &asset_tree_params,
        Some(height),
    );
    let root = asset_tree.root_node();

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
    let amount = 100;
    let nonce = b"test-nonce";

    let num_legs = 20;
    let mut legs = Vec::with_capacity(num_legs);
    let mut leg_encs = Vec::with_capacity(num_legs);
    let mut leg_enc_rands = Vec::with_capacity(num_legs);
    let mut asset_data_vec = Vec::with_capacity(num_legs);

    for _ in 0..num_legs {
        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);
        asset_data_vec.push(asset_data.clone());
    }

    let mut paths = Vec::new();
    // All legs use the same asset (index 0)
    let indices = vec![0; num_legs];
    for chunk in indices.chunks(M) {
        let path = asset_tree.get_paths_to_leaves(chunk).unwrap();
        paths.push(path);
    }

    println!("For tree with height {height}, L={L}, M={M} and {num_legs} legs");

    let clock = Instant::now();
    let proof = SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
        &mut rng,
        legs,
        leg_encs.clone(),
        leg_enc_rands,
        paths,
        asset_data_vec,
        &root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let proving_time = clock.elapsed();

    let mut rmc_1 = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
    let mut rmc_0 = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));

    let clock = Instant::now();
    proof
        .verify(
            &mut rng,
            leg_encs,
            &root,
            vec![],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_1, &mut rmc_0)),
        )
        .unwrap();

    verify_rmc(rmc_0, rmc_1).unwrap();
    let verifying_time = clock.elapsed();

    println!(
        "Proving time: {:?}, verifying time: {:?}, proof size: {} bytes",
        proving_time,
        verifying_time,
        proof.compressed_size()
    );
}

#[test]
fn combined_settlement_verification() {
    // 2 settlement proofs SHARING one prover/transcript, aggregated into a single BP via new_with_given_prover +
    // prove_with_rng (vs batch_settlement_verification, which keeps the proofs independent and only batches checks).
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;
    const M: usize = 8;

    let height = 6;

    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        0,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let mut all_asset_data = Vec::new();
    let mut commitments = Vec::new();
    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
    let enc_keys = vec![pk_a_e.0];
    let med_keys = vec![];

    for i in 0..(M + 1) {
        let asset_id = (i + 1) as u32;
        let ad = AssetData::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
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
    let root = asset_tree.root_node();

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
    let amount = 100;

    let batch_size = 2;
    let mut nonces = Vec::with_capacity(batch_size);
    for i in 0..batch_size {
        nonces.push(format!("nonce_{}", i).into_bytes());
    }

    // Shared provers
    let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut even_prover = Prover::new(
        &asset_tree_params.even_parameters.pc_gens(),
        even_transcript,
    );
    let mut odd_prover = Prover::new(&asset_tree_params.odd_parameters.pc_gens(), odd_transcript);

    let mut proofs = Vec::with_capacity(batch_size);
    let mut all_leg_encs = Vec::with_capacity(batch_size);

    let clock = Instant::now();

    for i in 0..batch_size {
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

        for j in 0..num_legs {
            // Reuse all_asset_data in loop
            let ad_idx = j % all_asset_data.len();
            let leg = Leg::new(
                pk_s_e.0,
                pk_r_e.0,
                amount,
                all_asset_data[ad_idx].id,
                vec![pk_a_e.0],
                vec![],
                vec![],
            )
            .unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
                .unwrap();

            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
            asset_data.push(all_asset_data[ad_idx].clone());
        }

        for chunk in (0..num_legs as u32).collect::<Vec<_>>().chunks(M) {
            let path = asset_tree.get_paths_to_leaves(chunk).unwrap();
            leaf_paths.push(path);
        }

        let proof = SettlementCreationProof::<L, M, _, _, _, _>::new_with_given_prover::<_, _, _>(
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
            &mut even_prover,
            &mut odd_prover,
        )
        .unwrap();

        proofs.push(proof);
        all_leg_encs.push(leg_encs);
    }

    let (even_bp, odd_bp) = prove_with_rng(
        even_prover,
        odd_prover,
        asset_tree_params.even_parameters.bp_gens(),
        asset_tree_params.odd_parameters.bp_gens(),
        &mut rng,
    )
    .unwrap();
    let proving_time = clock.elapsed();

    // Shared verifiers
    let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut even_verifier = Verifier::new(even_transcript);
    let mut odd_verifier = Verifier::new(odd_transcript);

    let verify_sigma_clock = Instant::now();
    for i in 0..batch_size {
        proofs[i]
            .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                all_leg_encs[i].clone(),
                &root,
                vec![],
                vec![],
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                None,
            )
            .unwrap();
    }
    let sigma_constraints_time = verify_sigma_clock.elapsed();

    let bp_clock = Instant::now();
    // Verify R1CS proof
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
    let bp_verification_time = bp_clock.elapsed();

    let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
    let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
    let mut even_verifier = Verifier::new(transcript_even);
    let mut odd_verifier = Verifier::new(transcript_odd);
    let mut rmc_0 = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));

    let verify_sigma_rmc_clock = Instant::now();
    for i in 0..batch_size {
        proofs[i]
            .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                all_leg_encs[i].clone(),
                &root,
                vec![],
                vec![],
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                Some(&mut rmc_1),
            )
            .unwrap();
    }
    let sigma_constraints_rmc_time = verify_sigma_rmc_clock.elapsed();

    let rmc_clock = Instant::now();
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
    let rmc_verification_time = rmc_clock.elapsed();

    println!(
        "Proving time = {:?}, sigma = {:?}, bp_only = {:?}, sigma_rmc = {:?}, rmc_only = {:?}, proof size = {} bytes",
        proving_time,
        sigma_constraints_time,
        bp_verification_time,
        sigma_constraints_rmc_time,
        rmc_verification_time,
        even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
    );
}

#[test]
fn six_leg_alternating_settlement() {
    // 6-leg settlement with an interleaved reveal/hide pattern (legs 0,2,4 reveal the asset id; 1,3,5 hide it and
    // need a curve-tree membership proof) — vs six_leg_grouped_settlement's first-3-reveal/last-3-hide split.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;
    const M: usize = 2;

    let height = 6;

    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        0,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
    let enc_keys = vec![pk_a_e.0];
    let med_keys = vec![];

    let mut all_asset_data = Vec::new();
    let mut commitments = Vec::new();
    for i in 0..6 {
        let asset_id = (i + 1) as u32;
        let asset_data = AssetData::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
        )
        .unwrap();
        commitments.push(asset_data.commitment);
        all_asset_data.push(asset_data);
    }

    let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
        &commitments,
        &asset_tree_params,
        Some(height),
    );
    let root = asset_tree.root_node();

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
    let amount = 100;

    let nonce = b"test-nonce";

    let mut legs = Vec::new();
    let mut leg_encs = Vec::new();
    let mut leg_enc_rands = Vec::new();

    let mut asset_data_vec = Vec::new();
    for i in 0..6 {
        let reveal_asset_id = i % 2 == 0;
        let asset_id = i + 1;

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();

        let (leg_enc, leg_enc_rand) = leg
            .encrypt(
                &mut rng,
                LegEncConfig {
                    visibility: PartyVisibility::FullVisibility,
                    reveal_asset_id,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);
        if !reveal_asset_id {
            asset_data_vec.push(all_asset_data[i as usize].clone());
        }
    }

    // Since M=2
    let leaf_paths = vec![
        asset_tree.get_paths_to_leaves(&[1, 3]).unwrap(),
        asset_tree.get_paths_to_leaves(&[5]).unwrap(),
    ];

    let clock = Instant::now();
    let proof = SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
        &mut rng,
        legs,
        leg_encs.clone(),
        leg_enc_rands,
        leaf_paths,
        asset_data_vec,
        &root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let proving_time = clock.elapsed();

    let verify_clock = Instant::now();
    proof
        .verify::<_, PallasParams, VestaParams>(
            &mut rng,
            leg_encs.clone(),
            &root,
            vec![vec![pk_a_e.0], vec![pk_a_e.0], vec![pk_a_e.0]],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();
    let verification_time = verify_clock.elapsed();

    println!(
        "6-leg alternating settlement (3 revealed, 3 hidden): Proving = {:?}, Verify = {:?}, proof size = {} bytes",
        proving_time,
        verification_time,
        proof.compressed_size()
    );
}

#[test]
fn six_leg_grouped_settlement() {
    // 6-leg settlement where the first 3 legs reveal the asset id and the last 3 hide it (vs the interleaved
    // pattern in six_leg_alternating_settlement) — checks the grouped reveal/hide layout still verifies.
    let mut rng = rand::thread_rng();

    const NUM_GENS: usize = 1 << 17;
    const L: usize = 64;
    const M: usize = 2;

    let height = 6;

    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 1;
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        num_auditors,
        0,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
    let enc_keys = vec![pk_a_e.0];
    let med_keys = vec![];

    let mut all_asset_data = Vec::new();
    let mut commitments = Vec::new();
    for i in 0..6 {
        let asset_id = (i + 1) as u32;
        let asset_data = AssetData::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
        )
        .unwrap();
        commitments.push(asset_data.commitment);
        all_asset_data.push(asset_data);
    }

    let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
        &commitments,
        &asset_tree_params,
        Some(height),
    );
    let root = asset_tree.root_node();

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
    let amount = 100;

    let nonce = b"test-nonce";

    let mut legs = Vec::new();
    let mut leg_encs = Vec::new();
    let mut leg_enc_rands = Vec::new();
    let mut asset_data_vec = Vec::new();

    for j in 0..6 {
        let reveal_asset_id = j < 3;
        let asset_id = j + 1;

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            vec![pk_a_e.0],
            vec![],
            vec![],
        )
        .unwrap();

        let (leg_enc, leg_enc_rand) = leg
            .encrypt(
                &mut rng,
                LegEncConfig {
                    visibility: PartyVisibility::FullVisibility,
                    reveal_asset_id,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        legs.push(leg);
        leg_encs.push(leg_enc);
        leg_enc_rands.push(leg_enc_rand);
        if !reveal_asset_id {
            asset_data_vec.push(all_asset_data[j as usize].clone());
        }
    }

    // Since M=2
    let leaf_paths = vec![
        asset_tree.get_paths_to_leaves(&[3, 4]).unwrap(),
        asset_tree.get_paths_to_leaves(&[5]).unwrap(),
    ];

    let clock = Instant::now();
    let proof = SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
        &mut rng,
        legs,
        leg_encs.clone(),
        leg_enc_rands,
        leaf_paths,
        asset_data_vec,
        &root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();
    let proving_time = clock.elapsed();

    let verify_clock = Instant::now();
    proof
        .verify::<_, PallasParams, VestaParams>(
            &mut rng,
            leg_encs.clone(),
            &root,
            vec![vec![pk_a_e.0], vec![pk_a_e.0], vec![pk_a_e.0]],
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            None,
        )
        .unwrap();
    let verification_time = verify_clock.elapsed();

    println!(
        "6-leg grouped settlement (3 revealed, 3 hidden): Proving = {:?}, Verify = {:?}, proof size = {} bytes",
        proving_time,
        verification_time,
        proof.compressed_size()
    );
}

#[test]
fn leg_creation_proof_rejects_missing_blinding_key() {
    let mut rng = rand::thread_rng();
    const NUM_GENS: usize = 1 << 13;
    const L: usize = 64;

    let label = b"leg-missing-blinding";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

    let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let num_auditors = 2u8;
    let num_mediators = 1u8;
    let asset_id = 1;

    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params-mb",
        num_auditors as u32,
        num_mediators as u32,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

    let keys_enc = (0..num_auditors)
        .map(|_| keygen_enc(&mut rng, enc_key_gen))
        .collect::<Vec<_>>();
    let keys_mediator = (0..num_mediators)
        .map(|_| keygen_sig(&mut rng, sig_key_gen))
        .collect::<Vec<_>>();

    let enc_keys: Vec<_> = keys_enc.iter().map(|(_, k)| k.0).collect();
    let med_keys: Vec<_> = keys_mediator.iter().map(|(_, k)| k.0).collect();

    let asset_data = AssetData::new(
        asset_id,
        enc_keys.clone(),
        med_keys.clone(),
        &asset_comm_params,
    )
    .unwrap();

    let set = vec![asset_data.commitment];
    let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
        &set,
        &asset_tree_params,
        Some(2),
    );

    let nonce = b"test-nonce-mb";
    let leg = Leg::new(
        pk_s_e.0,
        pk_r_e.0,
        100,
        asset_id,
        enc_keys.clone(),
        med_keys.clone(),
        vec![],
    )
    .unwrap();
    let (leg_enc, leg_enc_rand) = leg
        .encrypt(
            &mut rng,
            LegEncConfig {
                visibility: PartyVisibility::FullVisibility,
                reveal_asset_id: false,
            },
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

    let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = asset_tree.root_node();

    let proof = LegCreationProof::new::<_, PallasParams, VestaParams>(
        &mut rng,
        leg.clone(),
        leg_enc.clone(),
        leg_enc_rand.clone(),
        path,
        asset_data.clone(),
        &root,
        nonce,
        &asset_tree_params,
        &asset_comm_params,
        enc_key_gen,
        enc_gen,
    )
    .unwrap();

    assert!(
        proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                leg_enc.clone(),
                &root,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .is_ok()
    );

    let mut missing_enc_blinding = proof.clone();
    missing_enc_blinding
        .re_randomized_points
        .blindings_with_different_gen
        .remove(&1);
    assert!(
        missing_enc_blinding
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                leg_enc.clone(),
                &root,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .is_err()
    );

    let mut missing_med_blinding = proof.clone();
    missing_med_blinding
        .re_randomized_points
        .blindings_with_different_gen
        .remove(&(enc_keys.len() + 1));
    assert!(
        missing_med_blinding
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                leg_enc.clone(),
                &root,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .is_err()
    );
}

proptest! {
    #[test]
    fn prop_leg_encrypt_decrypt_roundtrip_small_ranges(
        amount in 10u64..1000,
        asset_id in 0u64..10,
        parties_see_each_other in any::<bool>(),
        reveal_asset_id in any::<bool>(),
    ) {
        // Invariant: encrypt then decrypt-as-sender/-as-receiver round-trips the amount+asset id for any small
        // values and any (parties_see_each_other, reveal_asset_id); counterparty pk shown iff parties_see_each_other.
        let mut rng = rand::thread_rng();
        let label = b"pt-roundtrip-small";

        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let (sk_s, pk_s) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_r, pk_r) = keygen_enc(&mut rng, enc_key_gen);

        let leg = Leg::new(
            pk_s.0,
            pk_r.0,
            amount,
            asset_id as u32,
            vec![],
            vec![],
            vec![],
        )
        .unwrap();

        let (leg_enc, _) = leg
            .encrypt(
                &mut rng,
                LegEncConfig {
                    visibility: if parties_see_each_other { PartyVisibility::FullVisibility } else { PartyVisibility::NoVisibility },
                    reveal_asset_id,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let (sender_pk, receiver_opt, sender_asset_id, sender_amount) =
            leg_enc.decrypt_as_sender(&sk_s.0, enc_gen).unwrap();
        assert_eq!(sender_pk, pk_s.0);
        assert_eq!(sender_asset_id, asset_id as u32);
        assert_eq!(sender_amount, amount);
        assert_eq!(receiver_opt.is_some(), parties_see_each_other);

        let (sender_opt, receiver_pk, receiver_asset_id, receiver_amount) =
            leg_enc.decrypt_as_receiver(&sk_r.0, enc_gen).unwrap();
        assert_eq!(receiver_pk, pk_r.0);
        assert_eq!(receiver_asset_id, asset_id as u32);
        assert_eq!(receiver_amount, amount);
        assert_eq!(sender_opt.is_some(), parties_see_each_other);

        assert_eq!(leg_enc.is_asset_id_revealed(), reveal_asset_id);
    }

    #[test]
    fn prop_settlement_leg_option_matrix(
        reveal_asset_id in any::<bool>(),
        parties_see_each_other in any::<bool>(),
        has_enc_keys in any::<bool>(),
        has_mediators in any::<bool>(),
        has_public_extra_keys in any::<bool>(),
    ) {
        // Invariant: across the full matrix of per-leg options (reveal_asset_id / parties_see_each_other / presence of
        // auditor, mediator, public extra keys), the leg_enc's flags, ephemeral-key fields, and key-list lengths match.
        prop_assume!(!(has_mediators && !has_enc_keys));

        let mut rng = rand::thread_rng();

        let label = b"test_label";

        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();
        let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();

        let amount = 100;
        let asset_id = 1;

        let (_sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let enc_key_pair = keygen_enc(&mut rng, enc_key_gen);
        let med_key_pair = keygen_sig(&mut rng, sig_key_gen);
        let public_enc_key_pair = keygen_enc(&mut rng, enc_key_gen);

        let enc_pk = enc_key_pair.1 .0;
        let med_pk = med_key_pair.1 .0;
        let public_enc_pk = public_enc_key_pair.1 .0;
        let sk_for_oob = keygen_enc(&mut rng, enc_key_gen).0;

        let enc_keys: Vec<_> = if has_enc_keys { vec![enc_pk] } else { vec![] };
        let med_keys: Vec<_> = if has_mediators {
            vec![med_pk]
        } else {
            vec![]
        };
        let public_enc_keys: Vec<_> = if has_public_extra_keys {
            vec![public_enc_pk]
        } else {
            vec![]
        };

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            public_enc_keys.clone(),
        )
        .unwrap();

        let config = LegEncConfig {
            visibility: if parties_see_each_other { PartyVisibility::FullVisibility } else { PartyVisibility::NoVisibility },
            reveal_asset_id,
        };

        let (leg_enc, _) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();

        if reveal_asset_id {
            assert!(leg_enc.is_asset_id_revealed());
            assert_eq!(leg_enc.asset_id(), Some(asset_id));
            assert!(leg_enc.asset_id_ciphertext().is_none());
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r4.is_none());
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r4.is_none());
        } else {
            assert!(!leg_enc.is_asset_id_revealed());
            assert!(leg_enc.asset_id_ciphertext().is_some());
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r4.is_some());
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r4.is_some());
        }

        assert_eq!(
            leg_enc.party_visibility() == PartyVisibility::FullVisibility,
            parties_see_each_other,
        );

        if parties_see_each_other {
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r2.is_some());
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r1.is_some());
        } else {
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_s.r2.is_none());
            assert!(leg_enc.leg_enc_core_and_eph_keys.eph_pk_r.r1.is_none());
        }

        assert_eq!(leg_enc.eph_pk_enc_keys.len(), enc_keys.len());
        assert_eq!(leg_enc.eph_pk_public_enc_keys.len(), public_enc_keys.len());
        // Mediator entries are only created when the asset-id is hidden. A revealed-asset leg carries
        // `None`, not an empty vec, and takes its mediators from the asset's registered ones.
        if reveal_asset_id {
            assert!(leg_enc.mediators.is_none());
        } else {
            assert_eq!(
                leg_enc.mediators.as_ref().map(|m| m.len()),
                Some(med_keys.len())
            );
        }

        assert!(
            leg_enc
                .decrypt_given_key(&sk_for_oob.0, false, enc_keys.len(), enc_gen)
                .is_err()
        );
        assert!(
            leg_enc
                .decrypt_given_key(&sk_for_oob.0, true, public_enc_keys.len(), enc_gen)
                .is_err()
        );

    }
}

proptest! {
    // Reducing number of runs to finish tests faster
    #![proptest_config(proptest::test_runner::Config { cases: 8, .. proptest::test_runner::Config::default() })]

    #[test]
    fn prop_leg_verification_rejects_bad_proof(
        parties_see_each_other in any::<bool>(),
        num_enc_keys in 0u8..2u8,
        num_mediators in 0u8..2u8,
        has_public_enc_keys in any::<bool>(),
    ) {
        // Invariant: a valid leg-creation proof, tampered each way (truncated sigma-response vectors, nulled r2/r1
        // cross-party proofs, or a leg_enc with an r4 ephemeral-key component removed), is always rejected by verify.
        prop_assume!(!(num_mediators > 0 && num_enc_keys == 0));
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        const HEIGHT: usize = 2;

        let label = b"test_label";
        let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label, NUM_GENS as u32, NUM_GENS as u32,
        ).unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"test_label_1",
            num_enc_keys as u32,
            num_mediators as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_enc = (0..num_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let enc_keys: Vec<_> = keys_enc.iter().map(|(_, k)| k.0).collect();
        let med_keys: Vec<_> = keys_mediator.iter().map(|(_, k)| k.0).collect();

        let pub_enc_keys: Vec<_> = if has_public_enc_keys {
            vec![keygen_enc(&mut rng, enc_key_gen).1 .0]
        } else {
            vec![]
        };

        let asset_id = 1u32;
        let amount = 100u64;
        let nonce = b"test-nonce";

        let asset_data = AssetData::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
        ).unwrap();

        let set = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set, &asset_tree_params, Some(HEIGHT),
        );
        let root = asset_tree.root_node();

        let leg = Leg::new(
            pk_s_e.0, pk_r_e.0, amount, asset_id,
            enc_keys, med_keys, pub_enc_keys.clone(),
        ).unwrap();

        let (leg_enc, leg_enc_rand) = leg.encrypt(
            &mut rng,
            LegEncConfig { visibility: if parties_see_each_other { PartyVisibility::FullVisibility } else { PartyVisibility::NoVisibility }, reveal_asset_id: false },
            enc_key_gen, enc_gen,
        ).unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let proof = LegCreationProof::<L, PallasScalar, VestaScalar, PallasConfig, VestaParameters>::new::<_, PallasParams, VestaParams>(
            &mut rng, leg, leg_enc.clone(), leg_enc_rand,
            path, asset_data, &root, nonce,
            &asset_tree_params, &asset_comm_params, enc_key_gen, enc_gen,
        ).unwrap();

        let verify_bad_proof = |rng: &mut _,
            p: &mut LegCreationProof<L, PallasScalar, VestaScalar, PallasConfig, VestaParameters>|
        {
            assert!(p.verify::<_, PallasParams, VestaParams>(
                rng, leg_enc.clone(), &root, pub_enc_keys.clone(), nonce,
                &asset_tree_params, &asset_comm_params, enc_key_gen, enc_gen, None,
            ).is_err());
        };

        proof.verify::<_, PallasParams, VestaParams>(
            &mut rng, leg_enc.clone(), &root, pub_enc_keys.clone(), nonce,
            &asset_tree_params, &asset_comm_params, enc_key_gen, enc_gen, None,
        ).unwrap();

        // shorter proof.resp_eph_pk_enc
        if !proof.resp_eph_pk_enc.is_empty() {
            let mut p = proof.clone();
            p.resp_eph_pk_enc.pop();
            verify_bad_proof(&mut rng, &mut p);
        }

        // shorter proof.resp_eph_pk_meds
        if leg_enc.num_mediators() > 0 {
            let mut p = proof.clone();
            p.resp_eph_pk_meds.pop();
            verify_bad_proof(&mut rng, &mut p);
        }

        // shorter proof.resp_eph_pk_public_enc
        if has_public_enc_keys {
            let mut p = proof.clone();
            p.resp_eph_pk_public_enc.pop();
            verify_bad_proof(&mut rng, &mut p);
        }

        // shorter proof.resp_comm_r_i_amount
        {
            let mut p = proof.clone();
            p.resp_comm_r_i_amount.0.pop();
            verify_bad_proof(&mut rng, &mut p);
        }

        // set proof.resp_eph_pk_s_r to None (remove sender's r2 proof)
        if parties_see_each_other {
            let mut p = proof.clone();
            p.resp_eph_pk_s_r = None;
            verify_bad_proof(&mut rng, &mut p);
        }

        // set proof.resp_eph_pk_r_s to None (remove receiver's r1 proof)
        if parties_see_each_other {
            let mut p = proof.clone();
            p.resp_eph_pk_r_s = None;
            verify_bad_proof(&mut rng, &mut p);
        }

        let verify_bad_leg_enc = |rng: &mut _, leg_enc: LegEncryption<PallasA>| {
            assert!(proof.verify::<_, PallasParams, VestaParams>(
                rng, leg_enc, &root, pub_enc_keys.clone(), nonce,
                &asset_tree_params, &asset_comm_params, enc_key_gen, enc_gen, None,
            ).is_err());
        };

        // leg_enc.eph_pk_s.r4 must be Some when asset-id is encrypted
        {
            let mut m = leg_enc.clone();
            m.leg_enc_core_and_eph_keys.eph_pk_s.r4 = None;
            verify_bad_leg_enc(&mut rng, m);
        }

        // leg_enc.eph_pk_r.r4 must be Some when asset-id is encrypted
        {
            let mut m = leg_enc.clone();
            m.leg_enc_core_and_eph_keys.eph_pk_r.r4 = None;
            verify_bad_leg_enc(&mut rng, m);
        }

        // leg_enc.eph_pk_enc_keys[i].r4 must be Some when asset-id is encrypted
        if !leg_enc.eph_pk_enc_keys.is_empty() {
            let mut m = leg_enc.clone();
            m.eph_pk_enc_keys[0].r4 = None;
            verify_bad_leg_enc(&mut rng, m);
        }

        // leg_enc.eph_pk_public_enc_keys[i].r4 must be Some when asset-id is encrypted
        if has_public_enc_keys {
            let mut m = leg_enc.clone();
            m.eph_pk_public_enc_keys[0].r4 = None;
            verify_bad_leg_enc(&mut rng, m);
        }
    }
}

proptest! {
    // Building and verifying a leg proof per case is expensive; keep the run count low.
    #![proptest_config(proptest::test_runner::Config { cases: 8, .. proptest::test_runner::Config::default() })]

    #[test]
    fn prop_investor_always_decrypts_verified_leg(
        reveal_asset_id in any::<bool>(),
        parties_see_each_other in any::<bool>(),
        num_enc_keys in 1u8..3,
        num_mediators in 0u8..2,
    ) {
        // Even an adversarial creator that produces a verifying leg-creation proof must leave the leg
        // decryptable by the investors' encryption keys alone, across both proof paths (hidden/revealed asset id).
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;

        let label = b"investor-decrypt";
        let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let asset_id = 1u32;
        let amount = 100u64;
        let nonce = b"test-nonce";

        let (sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_enc = (0..num_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let enc_secrets = keys_enc.iter().map(|(sk, _)| sk.0).collect::<Vec<_>>();
        let enc_keys = keys_enc.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        let med_keys = keys_mediator
            .iter()
            .map(|(_, k)| k.0)
            .collect::<Vec<_>>();

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            vec![],
        )
        .unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt(
                &mut rng,
                LegEncConfig {
                    visibility: if parties_see_each_other { PartyVisibility::FullVisibility } else { PartyVisibility::NoVisibility },
                    reveal_asset_id,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        if reveal_asset_id {
            let pc_gens = PedersenGens::<PallasA>::default();
            let bp_gens = BulletproofGens::<PallasA>::new(NUM_GENS as u32, 1);
            let proof = PublicAssetLegCreationProof::<PallasConfig>::new(
                &mut rng,
                leg,
                leg_enc.clone(),
                leg_enc_rand,
                nonce,
                &pc_gens,
                &bp_gens,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
            proof
                .verify(
                    &mut rng,
                    leg_enc.clone(),
                    asset_id,
                    enc_keys.clone(),
                    vec![],
                    nonce,
                    &pc_gens,
                    &bp_gens,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        } else {
            let asset_tree_params =
                SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
                    label,
                    NUM_GENS as u32,
                    NUM_GENS as u32,
                )
                .unwrap();
            let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
                b"asset-comm-params",
                num_enc_keys as u32,
                num_mediators as u32,
                &asset_tree_params.even_parameters.bp_gens(),
            );
            let asset_data = AssetData::new(
                asset_id,
                enc_keys.clone(),
                med_keys.clone(),
                &asset_comm_params,
            )
            .unwrap();
            let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
                &vec![asset_data.commitment],
                &asset_tree_params,
                Some(2),
            );
            let root = asset_tree.root_node();
            let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let proof = LegCreationProof::<L, PallasScalar, VestaScalar, PallasConfig, VestaParameters>::new::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                leg,
                leg_enc.clone(),
                leg_enc_rand,
                path,
                asset_data,
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    leg_enc.clone(),
                    &root,
                    vec![],
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        }

        // Investors recover the plaintext with their encryption keys alone.
        let (s, r, a, b) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
        assert_eq!(s, pk_s_e.0);
        assert_eq!(r.is_some(), parties_see_each_other);
        assert_eq!(a, asset_id);
        assert_eq!(b, amount);

        let (s, r, a, b) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
        assert_eq!(s.is_some(), parties_see_each_other);
        assert_eq!(r, pk_r_e.0);
        assert_eq!(a, asset_id);
        assert_eq!(b, amount);

        for (i, sk_enc) in enc_secrets.iter().enumerate() {
            let (s, r, a, b) = leg_enc.decrypt_given_key(sk_enc, false, i, enc_gen).unwrap();
            assert_eq!(s, pk_s_e.0);
            assert_eq!(r, pk_r_e.0);
            assert_eq!(a, asset_id);
            assert_eq!(b, amount);
        }
    }
}

#[test]
fn leg_creator_tries_to_portray_mediator_as_auditor() {
    // A leg creator registers an asset with a sole mediator, then proves against that leaf while
    // presenting the mediator key as a second auditor and claiming zero mediators. Both layouts commit
    // the same point block, so the mediator count under `count_gen` is what keeps the mediated leaf and
    // the all-auditor leaf distinct and the re-labelled layout is not the registered leaf.

    let mut rng = rand::thread_rng();
    const NUM_GENS: usize = 1 << 12;
    let label = b"test";
    let asset_tree_params =
        SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();
    let sig_key_gen = hash_to_pallas(label, b"sig-key-g").into_affine();
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
        b"asset-comm-params",
        2,
        2,
        &asset_tree_params.even_parameters.bp_gens(),
    );

    let asset_id = 1;
    let (_, ek0) = keygen_enc(&mut rng, enc_key_gen);
    let (_, mk0) = keygen_sig(&mut rng, sig_key_gen);

    // Mediated layout (1 enc, 1 mediator) vs mediator-less layout (2 enc, 0 mediators).
    let asset_a = AssetData::new(asset_id, vec![ek0.0], vec![mk0.0], &asset_comm_params).unwrap();
    let asset_b = AssetData::new(asset_id, vec![ek0.0, mk0.0], vec![], &asset_comm_params).unwrap();

    assert_ne!(
        asset_a.commitment, asset_b.commitment,
        "the mediator count must keep the mediated leaf distinct from the extra-auditor layout"
    );
    // Both layouts commit the same point block, so the divergence is exactly the mediator-count term.
    assert_eq!(
        (asset_a.commitment.into_group() - asset_b.commitment).into_affine(),
        asset_comm_params.count_gen()
    );
}

// Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

#[cfg(feature = "ignore_prover_input_sanitation")]
mod input_sanitation_disabled {
    use super::*;
    use crate::Error;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::leg::public_asset_leg_proof::PublicAssetLegCreationProof;
    use crate::leg::settlement_proof::LegProof;
    use ark_pallas::Affine as PallasA;
    use ark_std::UniformRand;
    use curve_tree_relations::curve_tree::Root;

    fn assert_leg_verify_fails_with_rmc(
        proof: &LegCreationProof<64, PallasScalar, VestaScalar, PallasParameters, VestaParameters>,
        rng: &mut impl CryptoRngCore,
        leg_enc: LegEncryption<PallasA>,
        root: &Root<64, 1, VestaParameters, PallasParameters>,
        nonce: &[u8],
        asset_tree_params: &SelRerandProofParametersNew<
            VestaParameters,
            PallasParameters,
            VestaParams,
            PallasParams,
        >,
        asset_comm_params: &AssetCommitmentParams<PallasParameters, VestaParameters>,
        enc_key_gen: PallasA,
        enc_gen: PallasA,
    ) {
        let verify_without_rmc = proof.verify::<_, PallasParams, VestaParams>(
            rng,
            leg_enc.clone(),
            root,
            vec![],
            nonce,
            asset_tree_params,
            asset_comm_params,
            enc_key_gen,
            enc_gen,
            None,
        );
        assert!(verify_without_rmc.is_err());

        let mut rmc_1 = RandomizedMultChecker::new(VestaScalar::rand(rng));
        let mut rmc_0 = RandomizedMultChecker::new(PallasScalar::rand(rng));
        let verify_with_rmc = proof.verify::<_, PallasParams, VestaParams>(
            rng,
            leg_enc,
            root,
            vec![],
            nonce,
            asset_tree_params,
            asset_comm_params,
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_1, &mut rmc_0)),
        );
        let rmc_result = verify_rmc(rmc_0, rmc_1);
        assert!(verify_with_rmc.is_err() || rmc_result.is_err());
    }

    #[test]
    fn leg_proof_with_mismatched_asset_data() {
        // Feeds the leg-proof verifier asset data that disagrees with the proof in 3 ways — leg asset id != committed
        // asset_data id, a mutated asset_data.id, and leg auditor/mediator keys != asset_data's — each must be rejected.
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;

        // Create public params (generators, etc)
        let asset_tree_params = SelRerandProofParametersNew::<
            VestaParameters,
            PallasParameters,
            _,
            _,
        >::new_using_label(
            b"asset-tree-params", NUM_GENS as u32, NUM_GENS as u32
        )
        .unwrap();

        let sig_key_gen = PallasA::rand(&mut rng);
        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);

        let num_auditors = 2u8;
        let num_mediators = 3u8;
        let asset_id = 1;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors as u32,
            num_mediators as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        // Encryption keys
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();
        let keys_auditor = keys_auditor.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        // Mediator affirmation keys
        let keys_mediator = keys_mediator.iter().map(|(_, k)| k.0).collect::<Vec<_>>();

        // Create asset_data with one asset_id
        let asset_data = AssetData::new(
            asset_id,
            keys_auditor.clone(),
            keys_mediator.clone(),
            &asset_comm_params,
        )
        .unwrap();

        let set = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set,
            &asset_tree_params,
            Some(2),
        );

        let amount = 100;
        let nonce = b"test-nonce";

        // Create a leg with a different asset_id than the one in asset_data
        let different_asset_id = asset_id + 1;
        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            different_asset_id,
            keys_auditor.clone(),
            keys_mediator.clone(),
            vec![],
        )
        .unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = asset_tree.root_node();

        let proof = LegCreationProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            path,
            asset_data.clone(),
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert_leg_verify_fails_with_rmc(
            &proof,
            &mut rng,
            leg_enc,
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );

        let mut asset_data_with_different_id = asset_data.clone();
        asset_data_with_different_id.id = different_asset_id;

        let (leg_enc_with_mutated_asset_data_id, leg_enc_rand_with_mutated_asset_data_id) = leg
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let proof_with_mutated_asset_data_id =
            LegCreationProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                leg.clone(),
                leg_enc_with_mutated_asset_data_id.clone(),
                leg_enc_rand_with_mutated_asset_data_id,
                path,
                asset_data_with_different_id,
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        assert_leg_verify_fails_with_rmc(
            &proof_with_mutated_asset_data_id,
            &mut rng,
            leg_enc_with_mutated_asset_data_id,
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );

        // Create different keys for the leg
        let different_keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let different_keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let different_keys_auditor = different_keys_auditor
            .iter()
            .map(|(_, k)| k.0)
            .collect::<Vec<_>>();
        // Mediator affirmation keys
        let different_keys_mediator = different_keys_mediator
            .iter()
            .map(|(_, k)| k.0)
            .collect::<Vec<_>>();

        // Create a leg with different auditor/mediator keys than those in asset_data
        let leg_with_diff_keys = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            different_keys_auditor.clone(),
            different_keys_mediator.clone(),
            vec![],
        )
        .unwrap();
        let (leg_enc, leg_enc_rand) = leg_with_diff_keys
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let proof = LegCreationProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            leg_with_diff_keys.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            path,
            asset_data.clone(),
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert_leg_verify_fails_with_rmc(
            &proof,
            &mut rng,
            leg_enc,
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );
    }

    #[test]
    fn leg_creation_proof_verifier_error_paths() {
        // Takes one valid (hidden-asset, cross-visible) leg proof and feeds verify mismatched public inputs: a leg_enc
        // with reveal_asset_id=true, one with parties_see_each_other=false, and truncated sigma responses — all rejected.
        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;

        let label = b"leg-verifier-errors";
        let asset_tree_params = SelRerandProofParametersNew::<
            VestaParameters,
            PallasParameters,
            _,
            _,
        >::new_using_label(label, NUM_GENS as u32, NUM_GENS as u32)
        .unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sig-key").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 2u8;
        let num_mediators = 1u8;
        let asset_id = 1;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors as u32,
            num_mediators as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_enc = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let enc_keys: Vec<_> = keys_enc.iter().map(|(_, k)| k.0).collect();
        let med_keys: Vec<_> = keys_mediator.iter().map(|(_, k)| k.0).collect();

        let asset_data = AssetData::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
        )
        .unwrap();

        let set = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set,
            &asset_tree_params,
            Some(2),
        );

        let amount = 100;
        let nonce = b"test-nonce";

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            vec![],
        )
        .unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt(
                &mut rng,
                LegEncConfig {
                    visibility: PartyVisibility::FullVisibility,
                    reveal_asset_id: false,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = asset_tree.root_node();

        let proof = LegCreationProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            path,
            asset_data.clone(),
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
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
                    vec![],
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_ok()
        );

        let leg_enc_revealed = {
            let (e, _) = leg
                .encrypt(
                    &mut rng,
                    LegEncConfig {
                        visibility: PartyVisibility::FullVisibility,
                        reveal_asset_id: true,
                    },
                    enc_key_gen,
                    enc_gen,
                )
                .unwrap();
            e
        };
        assert_leg_verify_fails_with_rmc(
            &proof,
            &mut rng,
            leg_enc_revealed,
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );

        let leg_enc_no_cross = {
            let (e, _) = leg
                .encrypt(
                    &mut rng,
                    LegEncConfig {
                        visibility: PartyVisibility::NoVisibility,
                        reveal_asset_id: false,
                    },
                    enc_key_gen,
                    enc_gen,
                )
                .unwrap();
            e
        };
        assert_leg_verify_fails_with_rmc(
            &proof,
            &mut rng,
            leg_enc_no_cross,
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );

        let mut mismatched_enc_resp_proof = proof.clone();
        mismatched_enc_resp_proof.resp_eph_pk_enc.pop();
        assert_leg_verify_fails_with_rmc(
            &mismatched_enc_resp_proof,
            &mut rng,
            leg_enc.clone(),
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );

        let mut mismatched_med_resp_proof = proof.clone();
        mismatched_med_resp_proof.resp_eph_pk_meds.pop();
        assert_leg_verify_fails_with_rmc(
            &mismatched_med_resp_proof,
            &mut rng,
            leg_enc.clone(),
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );

        let mut wrong_resp_len_proof = proof.clone();
        wrong_resp_len_proof.resp_comm_r_i_amount.0.pop();
        assert_leg_verify_fails_with_rmc(
            &wrong_resp_len_proof,
            &mut rng,
            leg_enc.clone(),
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        );
    }

    #[test]
    fn settlement_creation_proof_verifier_error_paths() {
        // Takes a valid 2-leg settlement proof and corrupts the leg_proofs vector — duplicating a leg proof (wrong
        // count vs leg_encs) and swapping a HiddenAssetProof leg for a RevealedAssetProof variant — each must be rejected.
        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 14;
        const L: usize = 64;
        const M: usize = 1;

        let label = b"settle-verifier-errors";
        let asset_tree_params = SelRerandProofParametersNew::<
            VestaParameters,
            PallasParameters,
            _,
            _,
        >::new_using_label(label, NUM_GENS as u32, NUM_GENS as u32)
        .unwrap();

        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 1u8;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors as u32,
            0,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
        let enc_keys_asset = vec![pk_a_e.0];

        let asset_id_1 = 1u32;
        let asset_id_2 = 2u32;
        let amount = 100;

        let asset_data_1 = AssetData::new(
            asset_id_1,
            enc_keys_asset.clone(),
            vec![],
            &asset_comm_params,
        )
        .unwrap();
        let asset_data_2 = AssetData::new(
            asset_id_2,
            enc_keys_asset.clone(),
            vec![],
            &asset_comm_params,
        )
        .unwrap();

        let commitments = vec![asset_data_1.commitment, asset_data_2.commitment];
        let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(2),
        );
        let root = asset_tree.root_node();
        let nonce = b"test-nonce";

        let leg_1 = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id_1,
            enc_keys_asset.clone(),
            vec![],
            vec![],
        )
        .unwrap();
        let leg_2 = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id_2,
            enc_keys_asset.clone(),
            vec![],
            vec![],
        )
        .unwrap();

        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt(
                &mut rng,
                LegEncConfig {
                    visibility: PartyVisibility::FullVisibility,
                    reveal_asset_id: false,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt(
                &mut rng,
                LegEncConfig {
                    visibility: PartyVisibility::FullVisibility,
                    reveal_asset_id: false,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let leaf_paths = vec![
            asset_tree.get_paths_to_leaves(&[0]).unwrap(),
            asset_tree.get_paths_to_leaves(&[1]).unwrap(),
        ];

        let proof =
            SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![leg_1.clone(), leg_2.clone()],
                vec![leg_enc_1.clone(), leg_enc_2.clone()],
                vec![leg_enc_rand_1.clone(), leg_enc_rand_2.clone()],
                leaf_paths,
                vec![asset_data_1, asset_data_2],
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![leg_enc_1.clone(), leg_enc_2.clone()],
                &root,
                vec![],
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let mut wrong_num_leg_encs = proof.clone();
        wrong_num_leg_encs
            .leg_proofs
            .push(wrong_num_leg_encs.leg_proofs[0].clone());
        assert!(
            wrong_num_leg_encs
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    vec![leg_enc_1.clone(), leg_enc_2.clone()],
                    &root,
                    vec![],
                    vec![],
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );

        let mut wrong_type_leg_proof = proof.clone();
        if let LegProof::HiddenAssetProof(p) = &wrong_type_leg_proof.leg_proofs[1] {
            let public_proof = PublicAssetLegCreationProof::<PallasConfig> {
                r1cs_proof: None,
                resp_amount_enc: p.resp_amount_enc.clone(),
                resp_ct_s: p.resp_ct_s.clone(),
                resp_ct_r: p.resp_ct_r.clone(),
                resp_eph_pk_s_v: p.resp_eph_pk_s_v.clone(),
                resp_eph_pk_r_v: p.resp_eph_pk_r_v.clone(),
                resp_eph_pk_s_r: p.resp_eph_pk_s_r.clone(),
                resp_eph_pk_r_s: p.resp_eph_pk_r_s.clone(),
                resp_eph_pk_enc: vec![],
                resp_eph_pk_public_enc: vec![],
                comm_r_i_amount: p.comm_r_i_amount,
                resp_comm_r_i_amount: p.resp_comm_r_i_amount.clone(),
            };
            wrong_type_leg_proof.leg_proofs[1] = LegProof::RevealedAssetProof(public_proof);
        }
        assert!(
            wrong_type_leg_proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    vec![leg_enc_1.clone(), leg_enc_2.clone()],
                    &root,
                    vec![],
                    vec![],
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .is_err()
        );
    }
}
