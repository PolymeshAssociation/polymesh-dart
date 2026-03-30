use super::*;
use crate::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc, keygen_sig};
use crate::leg::leg_proof::LegCreationProof;
use crate::leg::settlement_proof::SettlementCreationProof;
use crate::util::{
    add_verification_tuples_batches_to_rmc, batch_verify_bp, get_verification_tuples_with_rng,
    prove_with_rng, verify_rmc, verify_with_rng,
};
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_pallas::{Fq as PallasBase, Fr as PallasScalar, PallasConfig};
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;
use ark_vesta::{Fr as VestaScalar, VestaConfig};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use bulletproofs::r1cs::{Prover, Verifier};
use curve_tree_relations::curve_tree::CurveTree;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use std::time::Instant;

type PallasParameters = PallasConfig;
type VestaParameters = VestaConfig;
type PallasF = PallasScalar;
type VestaFr = PallasBase;
type PallasFr = PallasScalar;

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
    let med_keys = keys_mediator
        .iter()
        .enumerate()
        .map(|(i, (_, k))| (i as u8, k.0))
        .collect::<Vec<_>>();
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
                parties_see_each_other: true,
                reveal_asset_id: true,
            },
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

    assert!(leg_enc.is_asset_id_revealed());
    assert_eq!(leg_enc.asset_id_ciphertext(), None);

    let (s_pk, r_pk_opt, a_id, amt) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
    assert_eq!(s_pk, pk_s_e.0);
    assert_eq!(r_pk_opt, Some(pk_r_e.0));
    assert!(a_id.is_none()); // asset_id was revealed (not encrypted), so unavailable via sender decryption
    assert_eq!(amt, amount);

    let (s_pk_opt, r_pk, a_id, amt) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
    assert_eq!(s_pk_opt, Some(pk_s_e.0));
    assert_eq!(r_pk, pk_r_e.0);
    assert!(a_id.is_none()); // asset_id was revealed (not encrypted), so unavailable via receiver decryption
    assert_eq!(amt, amount);

    for (i, (sk_enc, _)) in keys_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, false, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert!(a_id.is_none());
        assert_eq!(amt, amount);
    }

    for (i, (sk_enc, _)) in keys_public_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, true, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert!(a_id.is_none());
        assert_eq!(amt, amount);
    }

    let (leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegEncConfig {
                parties_see_each_other: false,
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
    assert_eq!(a_id, Some(asset_id));
    assert_eq!(amt, amount);

    let (s_pk_opt, r_pk, a_id, amt) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
    assert_eq!(s_pk_opt, None);
    assert_eq!(r_pk, pk_r_e.0);
    assert_eq!(a_id, Some(asset_id));
    assert_eq!(amt, amount);

    for (i, (sk_enc, _)) in keys_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, false, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, Some(asset_id));
        assert_eq!(amt, amount);
    }

    for (i, (sk_enc, _)) in keys_public_enc.iter().enumerate() {
        let (s_pk, r_pk, a_id, amt) = leg_enc
            .decrypt_given_key(&sk_enc.0, true, i, enc_gen)
            .unwrap();
        assert_eq!(s_pk, pk_s_e.0);
        assert_eq!(r_pk, pk_r_e.0);
        assert_eq!(a_id, Some(asset_id));
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

    let mut test_with_config = |parties_see_each_other: bool,
                                num_enc_keys: u8,
                                num_mediators: u8,
                                num_public_enc_keys: u8,
                                num_public_mediators: u8| {
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            (num_enc_keys + num_mediators) as u32,
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

        let keys_enc = keys_enc.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        // Each mediator along with its index for encryption key
        let keys_mediator = keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| {
                (
                    if i < num_enc_keys as usize {
                        i as u8
                    } else {
                        (num_enc_keys - 1) as u8
                    },
                    k.0,
                )
            })
            .collect::<Vec<_>>();
        let public_enc_keys: Vec<_> = keys_public_enc.iter().map(|(_, k)| k.0).collect();

        let asset_data = AssetData::new(
            asset_id,
            keys_enc.clone(),
            keys_mediator.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.sl_params.delta,
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
            parties_see_each_other,
            reveal_asset_id: false, // asset-id is always hidden
        };

        let (leg_enc, leg_enc_rand) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = asset_tree.root_node();

        let proof = LegCreationProof::<L, PallasF, VestaFr, PallasConfig, VestaParameters>::new::<
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

        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let verifier_time_rmc = clock.elapsed();

        let (p1, p2, a, b) = leg_enc.decrypt_as_sender(&sk_s_e.0, enc_gen).unwrap();
        assert_eq!(p1, pk_s_e.0);
        if parties_see_each_other {
            assert_eq!(p2.unwrap(), pk_r_e.0);
        } else {
            assert!(p2.is_none());
        }
        assert_eq!(a, Some(asset_id));
        assert_eq!(b, amount);

        let (p1, p2, a, b) = leg_enc.decrypt_as_receiver(&sk_r_e.0, enc_gen).unwrap();
        if parties_see_each_other {
            assert_eq!(p1.unwrap(), pk_s_e.0);
        } else {
            assert!(p1.is_none());
        }
        assert_eq!(p2, pk_r_e.0);
        assert_eq!(a, Some(asset_id));
        assert_eq!(b, amount);

        println!(
            "parties_see_each_other={}, num_enc_keys={}, num_mediators={}, num_public_enc_keys={}, num_public_mediators={}, L={L}, height={}",
            parties_see_each_other,
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

    test_with_config(true, 2, 2, 1, 1);

    test_with_config(false, 2, 2, 1, 1);

    test_with_config(true, 0, 0, 0, 0);
    test_with_config(false, 0, 0, 0, 0);

    test_with_config(true, 0, 0, 1, 1);
    test_with_config(false, 0, 0, 1, 1);
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
            (num_auditors + num_mediators) as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let keys_auditor = keys_auditor.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        // Each mediator along with its index for encryption key
        let keys_mediator = keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| {
                (
                    if i < num_auditors as usize {
                        i as u8
                    } else {
                        (num_auditors - 1) as u8
                    },
                    k.0,
                )
            })
            .collect::<Vec<_>>();

        let mut asset_data_vec = Vec::with_capacity(batch_size);
        let mut commitments = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let asset_data = AssetData::new(
                asset_id,
                keys_auditor.clone(),
                keys_mediator.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.sl_params.delta,
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
            parties_see_each_other,
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

            let proof =
                LegCreationProof::<L, PallasF, VestaFr, PallasConfig, VestaParameters>::new::<
                    _,
                    PallasParams,
                    VestaParams,
                >(
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
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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

    let mut test_with_config = |parties_see_each_other: bool,
                                num_auditors: u8,
                                num_mediators: u8| {
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            (num_auditors + num_mediators) as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let keys_auditor = keys_auditor.iter().map(|(_, k)| k.0).collect::<Vec<_>>();
        // Each mediator along with its index for encryption key
        let keys_mediator = keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| {
                (
                    if i < num_auditors as usize {
                        i as u8
                    } else {
                        num_auditors.saturating_sub(1)
                    },
                    k.0,
                )
            })
            .collect::<Vec<_>>();

        let mut asset_data_vec = Vec::with_capacity(batch_size);
        let mut commitments = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let asset_data = AssetData::new(
                asset_id,
                keys_auditor.clone(),
                keys_mediator.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.sl_params.delta,
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
            parties_see_each_other,
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

            let proof = LegCreationProof::<L, PallasF, VestaFr, PallasConfig, VestaParameters>::new_with_given_prover::<_, PallasParams, VestaParams>(
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

            ).unwrap();
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
        let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

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
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
            asset_tree_params.odd_parameters.sl_params.delta,
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
                    parties_see_each_other: true,
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
                    parties_see_each_other: true,
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

        let (enc_keys, med_keys) = if !reveal_asset_id {
            (vec![], vec![])
        } else {
            // When asset IDs are revealed, provide encryption keys and mediator keys for verification
            // enc_keys: one Vec<Affine> per revealed asset leg
            // med_keys: one Vec<(u8, Affine)> per revealed asset leg (empty if no mediators)
            (vec![vec![pk_a_e.0], vec![pk_a_e.0]], vec![vec![], vec![]])
        };

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                vec![leg_enc1.clone(), leg_enc2.clone()],
                &root,
                enc_keys.clone(),
                med_keys.clone(),
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
                med_keys,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
                    parties_see_each_other: true,
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
                    parties_see_each_other: true,
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

        let (enc_keys, med_keys) = if !reveal_asset_id {
            (vec![], vec![])
        } else {
            (
                vec![
                    vec![pk_a_e.0],
                    vec![pk_a_e.0],
                    vec![pk_a_e.0],
                    vec![pk_a_e.0],
                ],
                vec![vec![], vec![], vec![], vec![]],
            )
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
                med_keys.clone(),
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
                med_keys,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
                    parties_see_each_other: true,
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

        let (enc_keys, med_keys) = if !reveal_asset_id {
            (vec![], vec![])
        } else {
            (
                vec![
                    vec![pk_a_e.0],
                    vec![pk_a_e.0],
                    vec![pk_a_e.0],
                    vec![pk_a_e.0],
                    vec![pk_a_e.0],
                ],
                vec![vec![], vec![], vec![], vec![], vec![]],
            )
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
                med_keys.clone(),
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
                med_keys,
                vec![],
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    for i in 0..batch_size {
        let (even, odd) = proofs[i]
            .verify_and_return_tuples(
                all_leg_encs[i].clone(),
                &root,
                vec![],
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
    verify_rmc(&rmc_0, &rmc_1).unwrap();
    let rmc_time = clock.elapsed();

    println!(
        "Verifier time = {:?}, batch tuple time {:?}, batch BP time {:?}, batch_tuple_rmc_time {:?}, batch_verifier_rmc_time {:?}",
        verifier_time, batch_tuple_time, batch_bp_time, batch_tuple_rmc_time, rmc_time
    );
}

#[test]
fn large_settlement_verification() {
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
        asset_tree_params.odd_parameters.sl_params.delta,
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

    // NOTE: The upstream `bulletproofs` fork used here has a fixed cap on transcript labels
    // for the `t` polynomial (`util::T_LABELS.len() == 401`), which limits the number of
    // vector commitments per aggregated R1CS proof. Keep this test below that cap.
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
            vec![],
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            Some((&mut rmc_1, &mut rmc_0)),
        )
        .unwrap();

    verify_rmc(&rmc_0, &rmc_1).unwrap();
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
    let root = asset_tree.root_node();

    let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
    let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
    let amount = 100;

    // See note in `large_settlement_verification` about the `t` polynomial label cap.
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
    let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
    let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

    let verify_sigma_rmc_clock = Instant::now();
    for i in 0..batch_size {
        proofs[i]
            .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                all_leg_encs[i].clone(),
                &root,
                vec![],
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
    verify_rmc(&rmc_0, &rmc_1).unwrap();
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
            asset_tree_params.odd_parameters.sl_params.delta,
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
                    parties_see_each_other: true,
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
            vec![vec![], vec![], vec![]],
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
            asset_tree_params.odd_parameters.sl_params.delta,
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
                    parties_see_each_other: true,
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
            vec![vec![], vec![], vec![]],
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

// Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

#[cfg(feature = "ignore_prover_input_sanitation")]
mod input_sanitation_disabled {
    use super::*;
    use crate::keys::{keygen_enc, keygen_sig};
    use ark_pallas::Affine as PallasA;
    use ark_std::UniformRand;
    use blake2::Blake2b512;

    #[test]
    fn settlement_proof_with_mismatched_asset_data() {
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
            (num_auditors + num_mediators) as u32,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        // Account signing (affirmation) keys
        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);

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
        // Each mediator along with its index for encryption key
        let keys_mediator = keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_auditors, k.0))
            .collect::<Vec<_>>();

        // Create asset_data with one asset_id
        let asset_data = AssetData::new(
            asset_id,
            keys_auditor.clone(),
            keys_mediator.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.sl_params.delta,
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

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc,
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
        // Each mediator along with its index for encryption key
        let different_keys_mediator = different_keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_auditors, k.0))
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

        assert!(
            proof
                .verify(
                    &mut rng,
                    leg_enc,
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
}
