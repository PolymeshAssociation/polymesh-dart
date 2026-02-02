use ark_pallas::Affine as PallasA;
use ark_std::UniformRand;
use blake2::Blake2b512;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use criterion::{Criterion, criterion_group, criterion_main};
use curve_tree_relations::curve_tree::CurveTree;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use polymesh_dart_bp::account::state::{AccountCommitmentKeyTrait, AccountState};
use polymesh_dart_bp::account::{AffirmAsReceiverTxnProof, AffirmAsSenderTxnProof};
use ark_ec_divisors::curves::{
    pallas::{PallasParams, Point as PallasPoint},
    vesta::{Point as VestaPoint, VestaParams},
};
use polymesh_dart_bp::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc, keygen_sig};
use polymesh_dart_bp::poseidon_impls::poseidon_2::params::pallas::get_poseidon2_params_for_2_1_hashing;
use polymesh_dart_bp::util::verify_rmc;
use ark_ec::CurveGroup;
use polymesh_dart_bp::leg_new::{Leg, LegEncryption, LegEncryptionRandomness};

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
        hash_to_pallas(label, b"id-gen").into_affine(),
    ]
}

fn create_shared_setup(label: &[u8]) -> (
    SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
    impl AccountCommitmentKeyTrait<PallasA>,
    PallasA,
    PallasA,
) {
    const NUM_GENS: usize = 1 << 12;

    let account_tree_params = SelRerandProofParametersNew::<PallasParameters, VestaParameters, PallasParams, VestaParams>::new::<PallasPoint, VestaPoint>(
        NUM_GENS as u32,
        NUM_GENS as u32,
    )
    .unwrap();

    let account_comm_key = setup_comm_key(label);

    let enc_key_gen = hash_to_pallas(b"bench-affirmation", b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(b"bench-affirmation", b"enc-key-h").into_affine();

    (account_tree_params, account_comm_key, enc_key_gen, enc_gen)
}

/// Generate all keys needed for benchmarks
fn create_keys<R: rand_core::CryptoRngCore, K: AccountCommitmentKeyTrait<PallasA>>(
    rng: &mut R,
    account_comm_key: &K,
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

fn create_leg_and_encryption<R: rand_core::CryptoRngCore>(
    rng: &mut R,
    pk_s: VerKey<PallasA>,
    pk_r: VerKey<PallasA>,
    pk_s_e: EncKey<PallasA>,
    pk_r_e: EncKey<PallasA>,
    pk_a_e: EncKey<PallasA>,
    enc_key_gen: PallasA,
    enc_gen: PallasA,
) -> (LegEncryption<PallasA>, LegEncryptionRandomness<PallasFr>) {
    let asset_id = 1;
    let amount = 100;

    let leg = Leg::new(pk_s.0, pk_r.0, vec![(true, pk_a_e.0)], amount, asset_id).unwrap();
    leg.encrypt::<_, Blake2b512>(rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
        .unwrap()
}

fn create_account_and_tree<R: rand_core::CryptoRngCore, K: AccountCommitmentKeyTrait<PallasA> + Clone>(
    rng: &mut R,
    sk: SigKey<PallasA>,
    account_comm_key: K,
    account_tree_params: &SelRerandProofParametersNew<PallasParameters, VestaParameters, PallasParams, VestaParams>,
) -> (
    AccountState<PallasA>,
    CurveTree<64, 1, PallasParameters, VestaParameters>,
) {
    let asset_id = 1;
    let id = PallasFr::rand(rng);
    let poseidon_config = get_poseidon2_params_for_2_1_hashing().unwrap();
    let mut account = AccountState::new(rng, id, sk.0, asset_id, 0, poseidon_config).unwrap();
    account.balance = 200;

    let account_comm = account.commit(account_comm_key.clone()).unwrap();
    let set = vec![account_comm.0];
    let account_tree = CurveTree::<64, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        &account_tree_params,
        Some(6),
    );

    (account, account_tree)
}

fn bench_sender_affirmation_verification(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((sk_s, pk_s), (_sk_s_e, pk_s_e), (_sk_r, pk_r), (_sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key, enc_key_gen);

    let (leg_enc, leg_enc_rand) = create_leg_and_encryption(
        &mut rng,
        pk_s,
        pk_r,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        enc_key_gen,
        enc_gen,
    );

    let (account, account_tree) =
        create_account_and_tree(&mut rng, sk_s, account_comm_key.clone(), &account_tree_params);

    let nonce = b"test-nonce";
    let amount = 100;
    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasPoint, VestaPoint, _, _>(
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

    c.bench_function("AffirmAsSenderTxnProof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
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
        });
    });
}

fn bench_receiver_affirmation_verification(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((_sk_s, pk_s), (_sk_s_e, pk_s_e), (sk_r, pk_r), (_sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key, enc_key_gen);

    let (leg_enc, leg_enc_rand) = create_leg_and_encryption(
        &mut rng,
        pk_s,
        pk_r,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        enc_key_gen,
        enc_gen,
    );

    let (account, account_tree) =
        create_account_and_tree(&mut rng, sk_r, account_comm_key.clone(), &account_tree_params);

    let nonce = b"test-nonce";
    let updated_account = account.get_state_for_receive();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, PallasPoint, VestaPoint, _, _>(
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

    c.bench_function("AffirmAsReceiverTxnProof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
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
        });
    });
}

fn bench_sender_affirmation_verification_with_rmc(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((sk_s, pk_s), (_sk_s_e, pk_s_e), (_sk_r, pk_r), (_sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key, enc_key_gen);

    let (leg_enc, leg_enc_rand) = create_leg_and_encryption(
        &mut rng,
        pk_s,
        pk_r,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        enc_key_gen,
        enc_gen,
    );

    let (account, account_tree) =
        create_account_and_tree(&mut rng, sk_s, account_comm_key.clone(), &account_tree_params);

    let nonce = b"test-nonce";
    let amount = 100;
    let updated_account = account.get_state_for_send(amount).unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasPoint, VestaPoint, _, _>(
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

    c.bench_function("AffirmAsSenderTxnProof verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));

            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
                    leg_enc.clone(),
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
        });
    });
}

fn bench_receiver_affirmation_verification_with_rmc(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
        create_shared_setup(b"bench-affirmation");

    let ((_sk_s, pk_s), (_sk_s_e, pk_s_e), (sk_r, pk_r), (_sk_r_e, pk_r_e), (_sk_a_e, pk_a_e)) =
        create_keys(&mut rng, &account_comm_key, enc_key_gen);

    let (leg_enc, leg_enc_rand) = create_leg_and_encryption(
        &mut rng,
        pk_s,
        pk_r,
        pk_s_e,
        pk_r_e,
        pk_a_e,
        enc_key_gen,
        enc_gen,
    );

    let (account, account_tree) =
        create_account_and_tree(&mut rng, sk_r, account_comm_key.clone(), &account_tree_params);

    let nonce = b"test-nonce";
    let updated_account = account.get_state_for_receive();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
    let root = account_tree.root_node();

    let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, PallasPoint, VestaPoint, _, _>(
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

    c.bench_function("AffirmAsReceiverTxnProof verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut local_rng));

            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut local_rng,
                    leg_enc.clone(),
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
