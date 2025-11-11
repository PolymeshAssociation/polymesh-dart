use ark_ec::CurveGroup;
use ark_pallas::Affine as PallasA;
use ark_std::{UniformRand, format};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use criterion::{Criterion, criterion_group, criterion_main};
use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use polymesh_dart_bp::account::NUM_GENERATORS;
use polymesh_dart_bp::account::state::AccountCommitmentKeyTrait;
use polymesh_dart_bp::fee_account::{FeeAccountState, FeeAccountTopupTxnProof, FeePaymentProof};
use polymesh_dart_bp::keys::{SigKey, keygen_sig};
use polymesh_dart_bp::util::verify_rmc;
use rand_core::CryptoRngCore;

type PallasParameters = ark_pallas::PallasConfig;
type VestaParameters = ark_vesta::VestaConfig;
type F0 = ark_pallas::Fr;
type F1 = ark_vesta::Fr;

/// Setup commitment key (duplicated from test module)
fn setup_comm_key(label: &[u8]) -> [PallasA; NUM_GENERATORS] {
    let account_comm_key: [PallasA; NUM_GENERATORS] = (0..NUM_GENERATORS)
        .map(|i| hash_to_pallas(label, format!("account-comm-{}", i).as_bytes()).into_affine())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    account_comm_key
}

/// Create new fee account (duplicated from test module)
fn new_fee_account<R: CryptoRngCore>(
    rng: &mut R,
    asset_id: u32,
    sk: SigKey<PallasA>,
    balance: u64,
) -> FeeAccountState<PallasA> {
    FeeAccountState::new(rng, sk.0, balance, asset_id).unwrap()
}

/// Create shared setup params for fee account benchmarks
fn create_shared_setup<R: CryptoRngCore>(
    _rng: &mut R,
) -> (
    SelRerandParameters<PallasParameters, VestaParameters>,
    [PallasA; NUM_GENERATORS],
) {
    const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)

    // Create public params (generators, etc)
    let account_tree_params = SelRerandParameters::<PallasParameters, VestaParameters>::new(
        NUM_GENS as u32,
        NUM_GENS as u32,
    )
    .unwrap();
    let account_comm_key = setup_comm_key(b"testing");

    (account_tree_params, account_comm_key)
}

/// Create a fee account and tree
fn create_fee_account_and_tree<R: CryptoRngCore>(
    rng: &mut R,
    asset_id: u32,
    sk: SigKey<PallasA>,
    balance: u64,
    account_comm_key: &[PallasA; NUM_GENERATORS],
    account_tree_params: &SelRerandParameters<PallasParameters, VestaParameters>,
) -> (
    FeeAccountState<PallasA>,
    CurveTree<2000, 1, PallasParameters, VestaParameters>,
) {
    let account = new_fee_account(rng, asset_id, sk, balance);
    let account_comm = account.commit(account_comm_key.clone()).unwrap();

    // This tree size can be chosen independently of the one used for regular accounts and will likely be bigger
    let set = vec![account_comm.0];
    let account_tree = CurveTree::<2000, 1, PallasParameters, VestaParameters>::from_leaves(
        &set,
        account_tree_params,
        Some(3),
    );

    (account, account_tree)
}

fn bench_fee_account_topup_verification(c: &mut Criterion) {
    let mut setup_rng = rand::thread_rng();

    let (account_tree_params, account_comm_key) = create_shared_setup(&mut setup_rng);

    let asset_id = 1;
    let balance = 1000;
    let increase_bal_by = 10;

    // Issuer creates keys
    let (sk_i, pk_i) = keygen_sig(&mut setup_rng, account_comm_key.sk_gen());

    let (account, account_tree) = create_fee_account_and_tree(
        &mut setup_rng,
        asset_id,
        sk_i,
        balance,
        &account_comm_key,
        &account_tree_params,
    );

    let nonce = b"test-nonce";
    let updated_account = account
        .get_state_for_topup(&mut setup_rng, increase_bal_by)
        .unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0);
    let root = account_tree.root_node();

    let (proof, nullifier) = FeeAccountTopupTxnProof::new(
        &mut setup_rng,
        &pk_i.0,
        increase_bal_by,
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
    )
    .unwrap();

    c.bench_function("FeeAccountTopupTxnProof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            proof
                .verify(
                    pk_i.0,
                    asset_id,
                    increase_bal_by,
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut local_rng,
                    None,
                )
                .unwrap();
        });
    });
}

fn bench_fee_account_topup_verification_with_rmc(c: &mut Criterion) {
    let mut setup_rng = rand::thread_rng();

    let (account_tree_params, account_comm_key) = create_shared_setup(&mut setup_rng);

    let asset_id = 1;
    let balance = 1000;
    let increase_bal_by = 10;

    // Issuer creates keys
    let (sk_i, pk_i) = keygen_sig(&mut setup_rng, account_comm_key.sk_gen());

    let (account, account_tree) = create_fee_account_and_tree(
        &mut setup_rng,
        asset_id,
        sk_i,
        balance,
        &account_comm_key,
        &account_tree_params,
    );

    let nonce = b"test-nonce";
    let updated_account = account
        .get_state_for_topup(&mut setup_rng, increase_bal_by)
        .unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0);
    let root = account_tree.root_node();

    let (proof, nullifier) = FeeAccountTopupTxnProof::new(
        &mut setup_rng,
        &pk_i.0,
        increase_bal_by,
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
    )
    .unwrap();

    c.bench_function("FeeAccountTopupTxnProof verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(F0::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(F1::rand(&mut local_rng));

            proof
                .verify(
                    pk_i.0,
                    asset_id,
                    increase_bal_by,
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut local_rng,
                    Some((&mut rmc_0, &mut rmc_1)),
                )
                .unwrap();
            verify_rmc(&rmc_0, &rmc_1).unwrap();
        });
    });
}

fn bench_fee_payment_verification(c: &mut Criterion) {
    let mut setup_rng = rand::thread_rng();

    let (account_tree_params, account_comm_key) = create_shared_setup(&mut setup_rng);

    let asset_id = 1;
    let balance = 1000;
    let fee_amount = 10;

    // Investor has fee payment account with some balance
    let (sk, _) = keygen_sig(&mut setup_rng, account_comm_key.sk_gen());

    let (account, account_tree) = create_fee_account_and_tree(
        &mut setup_rng,
        asset_id,
        sk,
        balance,
        &account_comm_key,
        &account_tree_params,
    );

    // Or could be hash(a_txn_id, a_payee_id)
    let nonce = b"a_txn_id,a_payee_id";
    let updated_account = account
        .get_state_for_payment(&mut setup_rng, fee_amount)
        .unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0);
    let root = account_tree.root_node();

    let (proof, nullifier) = FeePaymentProof::new(
        &mut setup_rng,
        fee_amount,
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
    )
    .unwrap();

    c.bench_function("FeePaymentProof verification", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            proof
                .verify(
                    asset_id,
                    fee_amount,
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut local_rng,
                    None,
                )
                .unwrap();
        });
    });
}

fn bench_fee_payment_verification_with_rmc(c: &mut Criterion) {
    let mut setup_rng = rand::thread_rng();

    let (account_tree_params, account_comm_key) = create_shared_setup(&mut setup_rng);

    let asset_id = 1;
    let balance = 1000;
    let fee_amount = 10;

    // Investor has fee payment account with some balance
    let (sk, _) = keygen_sig(&mut setup_rng, account_comm_key.sk_gen());

    let (account, account_tree) = create_fee_account_and_tree(
        &mut setup_rng,
        asset_id,
        sk,
        balance,
        &account_comm_key,
        &account_tree_params,
    );

    // Or could be hash(a_txn_id, a_payee_id)
    let nonce = b"a_txn_id,a_payee_id";
    let updated_account = account
        .get_state_for_payment(&mut setup_rng, fee_amount)
        .unwrap();
    let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
    let path = account_tree.get_path_to_leaf_for_proof(0, 0);
    let root = account_tree.root_node();

    let (proof, nullifier) = FeePaymentProof::new(
        &mut setup_rng,
        fee_amount,
        &account,
        &updated_account,
        updated_account_comm,
        path,
        &root,
        nonce,
        &account_tree_params,
        account_comm_key.clone(),
    )
    .unwrap();

    c.bench_function("FeePaymentProof verification with RMC", |b| {
        b.iter(|| {
            let mut local_rng = rand::thread_rng();
            let mut rmc_0 = RandomizedMultChecker::new(F0::rand(&mut local_rng));
            let mut rmc_1 = RandomizedMultChecker::new(F1::rand(&mut local_rng));

            proof
                .verify(
                    asset_id,
                    fee_amount,
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut local_rng,
                    Some((&mut rmc_0, &mut rmc_1)),
                )
                .unwrap();
            verify_rmc(&rmc_0, &rmc_1).unwrap();
        });
    });
}

criterion_group!(
    benches,
    bench_fee_account_topup_verification,
    bench_fee_account_topup_verification_with_rmc,
    bench_fee_payment_verification,
    bench_fee_payment_verification_with_rmc
);
criterion_main!(benches);
