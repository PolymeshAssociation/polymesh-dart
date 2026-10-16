#![allow(deprecated)]

use ark_ec::CurveGroup;
use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
use ark_pallas::Affine as PallasA;
use ark_std::UniformRand;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use criterion::{Criterion, criterion_group, criterion_main};
use curve_tree_relations::curve_tree::CurveTree;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use polymesh_dart_bp::account::state::{AccountCommitmentKeyTrait, AccountState};
use polymesh_dart_bp::account::{
    AccountTxnWitness, AffirmAsReceiverTxnProof, AffirmAsSenderTxnProof,
};
use polymesh_dart_bp::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc, keygen_sig};
use polymesh_dart_bp::leg::{Leg, LegEncConfig, LegEncryption, PartyVisibility};
use polymesh_dart_bp::poseidon_impls::poseidon_2::params::pallas::get_poseidon2_params_for_2_1_hashing;
use polymesh_dart_bp::util::verify_rmc;

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;
type PallasFr = ark_pallas::Fr;
type VestaFr = ark_vesta::Fr;

fn setup_comm_key(label: &[u8]) -> impl AccountCommitmentKeyTrait<PallasA> {
    [
        hash_to_pallas(label, b"sk-gen").into_affine(),
        hash_to_pallas(label, b"balance-gen").into_affine(),
        hash_to_pallas(label, b"counter-gen").into_affine(),
        hash_to_pallas(label, b"asset-id-gen").into_affine(),
        hash_to_pallas(label, b"rho-gen").into_affine(),
        hash_to_pallas(label, b"current-rho-gen").into_affine(),
        hash_to_pallas(label, b"randomness-gen").into_affine(),
        hash_to_pallas(label, b"current-randomness-gen").into_affine(),
        hash_to_pallas(label, b"id-gen").into_affine(),
        hash_to_pallas(label, b"sk-enc-inv-gen").into_affine(),
    ]
}

fn create_shared_setup(
    label: &[u8],
) -> (
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
) {
    const NUM_GENS: usize = 1 << 12;

    let account_tree_params = SelRerandProofParametersNew::<
        PallasParameters,
        VestaParameters,
        PallasParams,
        VestaParams,
    >::new(NUM_GENS as u32, NUM_GENS as u32)
    .unwrap();

    let account_comm_key = setup_comm_key(label);

    let enc_gen = hash_to_pallas(b"bench-affirmation", b"enc-key-h").into_affine();

    (account_tree_params, account_comm_key, enc_gen)
}

/// Generate all keys needed for benchmarks
fn create_keys<R: rand_core::CryptoRngCore, K: AccountCommitmentKeyTrait<PallasA>>(
    rng: &mut R,
    account_comm_key: &K,
) -> (
    (SigKey<PallasA>, VerKey<PallasA>),
    (DecKey<PallasA>, EncKey<PallasA>),
    (SigKey<PallasA>, VerKey<PallasA>),
    (DecKey<PallasA>, EncKey<PallasA>),
    (DecKey<PallasA>, EncKey<PallasA>),
) {
    let (sk_s, pk_s) = keygen_sig(rng, account_comm_key.sk_gen());
    let (sk_s_e, pk_s_e) = keygen_enc(rng, account_comm_key.sk_enc_gen());

    let (sk_r, pk_r) = keygen_sig(rng, account_comm_key.sk_gen());
    let (sk_r_e, pk_r_e) = keygen_enc(rng, account_comm_key.sk_enc_gen());

    let (sk_a_e, pk_a_e) = keygen_enc(rng, account_comm_key.sk_enc_gen());

    (
        (sk_s, pk_s),
        (sk_s_e, pk_s_e),
        (sk_r, pk_r),
        (sk_r_e, pk_r_e),
        (sk_a_e, pk_a_e),
    )
}

fn create_leg_and_encryption<R: rand_core::CryptoRngCore>(
    rng: &mut R,
    pk_s_e: EncKey<PallasA>,
    pk_r_e: EncKey<PallasA>,
    pk_a_e: EncKey<PallasA>,
    enc_key_gen: PallasA,
    enc_gen: PallasA,
    reveal_asset_id: bool,
) -> LegEncryption<PallasA> {
    let asset_id = 1;
    let amount = 100;

    let conf = LegEncConfig {
        visibility: PartyVisibility::FullVisibility,
        reveal_asset_id,
    };

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
    let (leg_enc, _) = leg.encrypt(rng, conf, enc_key_gen, enc_gen).unwrap();
    leg_enc
}

fn create_account_and_tree<
    R: rand_core::CryptoRngCore,
    K: AccountCommitmentKeyTrait<PallasA> + Clone,
>(
    rng: &mut R,
    sk_aff: SigKey<PallasA>,
    sk_enc: DecKey<PallasA>,
    account_comm_key: K,
    account_tree_params: &SelRerandProofParametersNew<
        PallasParameters,
        VestaParameters,
        PallasParams,
        VestaParams,
    >,
) -> (
    AccountState<PallasA>,
    CurveTree<64, 1, PallasParameters, VestaParameters>,
) {
    let asset_id = 1;
    let id = PallasFr::rand(rng);
    let poseidon_config = get_poseidon2_params_for_2_1_hashing().unwrap();
    let pk_aff = (account_comm_key.sk_gen() * sk_aff.0).into_affine();
    let pk_enc = (account_comm_key.sk_enc_gen() * sk_enc.0).into_affine();
    let (mut account, _) =
        AccountState::new(rng, id, pk_aff, pk_enc, asset_id, 0, poseidon_config).unwrap();
    account.balance = 200;

    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let set = vec![account_comm.0];
    let account_tree = CurveTree::<64, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(5),
    );

    (account, account_tree)
}

fn bench_sender_affirmation_verification(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((sk_s, _pk_s), (sk_s_e, pk_s_e), (_sk_r, _pk_r), (_sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key);

    let leg_enc = create_leg_and_encryption(
        &mut rng,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        account_comm_key.sk_enc_gen(),
        enc_gen,
        false,
    );

    let (account, account_tree) = create_account_and_tree(
        &mut rng,
        sk_s.clone(),
        sk_s_e.clone(),
        account_comm_key.clone(),
        &account_tree_params,
    );

    let nonce = b"test-nonce";
    let amount = 100;
    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, _, _>(
        &mut rng,
        {
            let (c, e) = leg_enc.core_and_eph_keys_for_sender();
            (c, e, amount)
        },
        AccountTxnWitness::new(
            sk_s.0.clone(),
            sk_s_e.0.clone(),
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

    c.bench_function("AffirmAsSenderTxnProof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
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
        });
    });
}

fn bench_receiver_affirmation_verification(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((_sk_s, _pk_s), (_sk_s_e, pk_s_e), (sk_r, _pk_r), (sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key);
    let leg_enc = create_leg_and_encryption(
        &mut rng,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        account_comm_key.sk_enc_gen(),
        enc_gen,
        false,
    );

    let (account, account_tree) = create_account_and_tree(
        &mut rng,
        sk_r.clone(),
        sk_r_e.clone(),
        account_comm_key.clone(),
        &account_tree_params,
    );

    let nonce = b"test-nonce";
    let updated_account = account.get_state_for_receive();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, _, _>(
        &mut rng,
        {
            let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
            (c, e, 100)
        },
        AccountTxnWitness::new(
            sk_r.0.clone(),
            sk_r_e.0.clone(),
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

    c.bench_function("AffirmAsReceiverTxnProof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
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
        });
    });
}

fn bench_sender_affirmation_verification_with_rmc(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((sk_s, _pk_s), (sk_s_e, pk_s_e), (_sk_r, _pk_r), (_sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key);

    let leg_enc = create_leg_and_encryption(
        &mut rng,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        account_comm_key.sk_enc_gen(),
        enc_gen,
        false,
    );

    let (account, account_tree) = create_account_and_tree(
        &mut rng,
        sk_s.clone(),
        sk_s_e.clone(),
        account_comm_key.clone(),
        &account_tree_params,
    );

    let nonce = b"test-nonce";
    let amount = 100;
    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, _, _>(
        &mut rng,
        {
            let (c, e) = leg_enc.core_and_eph_keys_for_sender();
            (c, e, amount)
        },
        AccountTxnWitness::new(
            sk_s.0.clone(),
            sk_s_e.0.clone(),
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

    // Fixed-base MSM vs combined MSM, per-proof BP verification.
    #[cfg(feature = "build-tables")]
    {
        use bulletproofs::r1cs::verify_given_verification_tuple;
        use curve_tree_relations::fixed_base_tables::{FixedBaseTables, FixedBaseTablesPair};
        use polymesh_dart_bp::util::verify_tuples_with_tables;

        let (even, odd) = proof
            .verify_and_return_tuples(
                leg_enc.core_and_eph_keys_for_sender(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let even_pc = account_tree_params.even_parameters.pc_gens();
        let odd_pc = account_tree_params.odd_parameters.pc_gens();
        let even_bp = account_tree_params.even_parameters.bp_gens();
        let odd_bp = account_tree_params.odd_parameters.bp_gens();
        let even_n = even.padded_n().unwrap();
        let odd_n = odd.padded_n().unwrap();
        let tables = FixedBaseTablesPair {
            even: FixedBaseTables::with_capacity(even_bp, even_n),
            odd: FixedBaseTables::with_capacity(odd_bp, odd_n),
        };
        println!(
            "SenderAffirm fixed-base tables: even padded_n={even_n}, odd padded_n={odd_n}; table size = {:.2} MB (even {:.2} + odd {:.2})",
            tables.table_bytes() as f64 / (1024.0 * 1024.0),
            tables.even.table_bytes() as f64 / (1024.0 * 1024.0),
            tables.odd.table_bytes() as f64 / (1024.0 * 1024.0),
        );

        c.bench_function("SenderAffirm per-proof BP verify: without tables", |b| {
            b.iter(|| {
                let (er, or) = rayon::join(
                    || verify_given_verification_tuple(even.clone(), even_pc, even_bp),
                    || verify_given_verification_tuple(odd.clone(), odd_pc, odd_bp),
                );
                er.unwrap();
                or.unwrap();
            });
        });

        c.bench_function("SenderAffirm per-proof BP verify: fixed-base tables", |b| {
            b.iter(|| {
                verify_tuples_with_tables(even.clone(), odd.clone(), even_pc, odd_pc, &tables)
                    .unwrap();
            });
        });

        // Table-aware host MSM, compared with plain msm_unchecked.
        {
            use ark_ec::VariableBaseMSM;
            use ark_ec::scalar_mul::fixed_base::FixedBaseMSM;
            use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
            use ark_host_msm_impl::table_cache::CurveTable;
            use ark_host_msm_impl::{
                CurveMSMId, clear_tables, host_msm_unchecked, register_table,
                register_table_with_given_size,
            };
            use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
            use bulletproofs::{BulletproofGens, PedersenGens};
            use std::collections::HashSet;
            use std::time::Instant;

            // The fixed base set for a BP proofs: B, B_blinding, then the padded G and H generators.
            fn fixed_gens<P: SWCurveConfig>(
                pc: &PedersenGens<Affine<P>>,
                bp: &BulletproofGens<Affine<P>>,
                n: u32,
            ) -> Vec<Affine<P>> {
                let mut v = Vec::with_capacity(2 + 2 * n as usize);
                v.push(pc.B);
                v.push(pc.B_blinding);
                v.extend(bp.G(n, 1).copied());
                v.extend(bp.H(n, 1).copied());
                v
            }

            fn host_buffer<P: SWCurveConfig>(
                pts: &[Affine<P>],
                scal: &[P::ScalarField],
            ) -> Vec<u8> {
                let name = <Projective<P> as VariableBaseMSM>::curve_name().unwrap();
                let id = CurveMSMId::from_curve_name(name);
                let mut b = Vec::new();
                id.serialize_uncompressed(&mut b).unwrap();
                pts.serialize_uncompressed(&mut b).unwrap();
                scal.serialize_uncompressed(&mut b).unwrap();
                b
            }

            fn host_run<P: SWCurveConfig>(buffer: &[u8]) -> Projective<P> {
                let mut buffer = buffer.to_vec();
                let len = buffer.len() as u32;
                let res_len = host_msm_unchecked(&mut buffer, len) as usize;
                Projective::<P>::deserialize_uncompressed_unchecked(&buffer[..res_len]).unwrap()
            }

            let fb_e = fixed_gens(even_pc, even_bp, even_n);
            let fb_o = fixed_gens(odd_pc, odd_bp, odd_n);

            let mut rmc_e = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
            let mut rmc_o = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    leg_enc.core_and_eph_keys_for_sender(),
                    &root,
                    updated_account_comm,
                    nullifier,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    Some((&mut rmc_e, &mut rmc_o)),
                )
                .unwrap();
            let (pts_e, scal_e) = rmc_e.points_and_scalars_for_msm();
            let (pts_o, scal_o) = rmc_o.points_and_scalars_for_msm();

            // Table-aware MSM with window of 10 bits.
            let table_e = CurveTable::<PallasParameters>::new_given_window_size(&fb_e, 10);
            let table_o = CurveTable::<VestaParameters>::new_given_window_size(&fb_o, 10);

            assert_eq!(
                Projective::<PallasParameters>::msm_unchecked(&pts_e, &scal_e),
                table_e.table_aware_msm(&pts_e, &scal_e),
                "even table-aware != plain",
            );
            assert_eq!(
                Projective::<VestaParameters>::msm_unchecked(&pts_o, &scal_o),
                table_o.table_aware_msm(&pts_o, &scal_o),
                "odd table-aware != plain",
            );

            let set_e: HashSet<Affine<PallasParameters>> = fb_e.iter().copied().collect();
            let set_o: HashSet<Affine<VestaParameters>> = fb_o.iter().copied().collect();
            let matches_e = pts_e.iter().filter(|p| set_e.contains(*p)).count();
            let matches_o = pts_o.iter().filter(|p| set_o.contains(*p)).count();
            println!(
                "Affirmation RMC-set MSM: even |bases|={} fixed {matches_e}/{}; odd |bases|={} fixed {matches_o}/{}",
                pts_e.len(),
                fb_e.len(),
                pts_o.len(),
                fb_o.len(),
            );

            c.bench_function("Affirmation RMC-set MSM: host without table", |b| {
                b.iter(|| {
                    let _ = Projective::<PallasParameters>::msm_unchecked(&pts_e, &scal_e);
                    let _ = Projective::<VestaParameters>::msm_unchecked(&pts_o, &scal_o);
                });
            });
            c.bench_function("Affirmation RMC-set MSM: table-aware host", |b| {
                b.iter(|| {
                    let _ = table_e.table_aware_msm(&pts_e, &scal_e);
                    let _ = table_o.table_aware_msm(&pts_o, &scal_o);
                });
            });

            // Route the same set through host_msm_unchecked with tables cleared vs registered.
            let buf_e = host_buffer::<PallasParameters>(&pts_e, &scal_e);
            let buf_o = host_buffer::<VestaParameters>(&pts_o, &scal_o);

            clear_tables();

            let plain_he = host_run::<PallasParameters>(&buf_e);
            let plain_ho = host_run::<VestaParameters>(&buf_o);

            register_table::<PallasParameters>(&fb_e);
            register_table::<VestaParameters>(&fb_o);

            assert_eq!(
                host_run::<PallasParameters>(&buf_e),
                plain_he,
                "host even: table-aware != plain",
            );
            assert_eq!(
                host_run::<VestaParameters>(&buf_o),
                plain_ho,
                "host odd: table-aware != plain",
            );

            clear_tables();

            c.bench_function("Affirmation host_msm_unchecked: no tables", |b| {
                clear_tables();
                b.iter(|| {
                    let _ = host_run::<PallasParameters>(&buf_e);
                    let _ = host_run::<VestaParameters>(&buf_o);
                });
            });

            c.bench_function("Affirmation host_msm_unchecked: with tables", |b| {
                register_table::<PallasParameters>(&fb_e);
                register_table::<VestaParameters>(&fb_o);
                b.iter(|| {
                    let _ = host_run::<PallasParameters>(&buf_e);
                    let _ = host_run::<VestaParameters>(&buf_o);
                });
                clear_tables();
            });

            // Window-size comparison through the host path. Prints the memory/speed tradeoff of
            // the window.

            let table_mb = |c: usize| -> f64 {
                (FixedBaseMSM::<PallasParameters>::new_given_window_size(&fb_e, c).table_bytes()
                    + FixedBaseMSM::<VestaParameters>::new_given_window_size(&fb_o, c)
                        .table_bytes()) as f64
                    / (1024.0 * 1024.0)
            };

            let time_host = |reps: u32| -> std::time::Duration {
                let t = Instant::now();
                for _ in 0..reps {
                    let _ = host_run::<PallasParameters>(&buf_e);
                    let _ = host_run::<VestaParameters>(&buf_o);
                }
                t.elapsed() / reps
            };

            let reps = 50u32;
            println!(
                "\n=== Affirmation host_msm_unchecked: window-size sweep (even+odd, {} fixed bases/side) ===",
                fb_e.len()
            );
            println!(
                "{:>6} | {:>8} | {:>13} | {:>8}",
                "window", "mem MB", "time", "speedup"
            );

            clear_tables();

            let off = time_host(reps);

            println!("{:>6} | {:>8} | {:>13?} | {:>8}", "off", "-", off, "1.00x");

            for &c in &[8usize, 10, 12, 14, 16] {
                register_table_with_given_size::<PallasParameters>(&fb_e, c);
                register_table_with_given_size::<VestaParameters>(&fb_o, c);
                let on = time_host(reps);
                println!(
                    "{:>6} | {:>8.2} | {:>13?} | {:>7.2}x",
                    c,
                    table_mb(c),
                    on,
                    off.as_secs_f64() / on.as_secs_f64()
                );
            }

            clear_tables();
        }
    }

    c.bench_function("AffirmAsSenderTxnProof verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));

            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
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
        });
    });
}

fn bench_receiver_affirmation_verification_with_rmc(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((_sk_s, _pk_s), (_sk_s_e, pk_s_e), (sk_r, _pk_r), (sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key);

    let leg_enc = create_leg_and_encryption(
        &mut rng,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        account_comm_key.sk_enc_gen(),
        enc_gen,
        false,
    );

    let (account, account_tree) = create_account_and_tree(
        &mut rng,
        sk_r.clone(),
        sk_r_e.clone(),
        account_comm_key.clone(),
        &account_tree_params,
    );

    let nonce = b"test-nonce";
    let updated_account = account.get_state_for_receive();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, _, _>(
        &mut rng,
        {
            let (c, e) = leg_enc.core_and_eph_keys_for_receiver();
            (c, e, 100)
        },
        AccountTxnWitness::new(
            sk_r.0.clone(),
            sk_r_e.0.clone(),
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

    c.bench_function("AffirmAsReceiverTxnProof verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));

            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
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
        });
    });
}

criterion_group!(
    benches,
    bench_sender_affirmation_verification,
    bench_receiver_affirmation_verification,
    bench_sender_affirmation_verification_with_rmc,
    bench_receiver_affirmation_verification_with_rmc
);
criterion_main!(benches);
