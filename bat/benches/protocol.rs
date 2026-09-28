use ark_ec::{AffineRepr, pairing::Pairing};
use ark_std::rand::{SeedableRng, rngs::StdRng};
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultCheckerGuard;
use std::hint::black_box;

use polymesh_bat::{
    Error,
    hash::HashToG1,
    protocol::{
        ClientSession, CommitmentToSigMask, IssuerKeypair, IssuerSession, OnChainIssuanceRequest,
        Payment, PreToken, RefundKey, RefundRequest, Reveal,
    },
};

type D = ark_pallas::Affine;

const ISSUANCE: &[u32] = &[1, 10, 100];
/// `(tokens, issuer keys)`.
const SPEND: &[(usize, usize)] = &[(1, 1), (8, 1), (8, 8), (32, 1), (32, 32)];
const REFUND: &[usize] = &[1, 10, 100];
const REVEALS: usize = 100;

fn issue<E: Pairing>(
    rng: &mut StdRng,
    keys: &IssuerKeypair<E>,
    count: u32,
) -> (Vec<PreToken<E, D>>, RefundKey<D>)
where
    E: HashToG1,
{
    let (session, request) = ClientSession::<E, D>::new(rng, count, &D::generator()).unwrap();
    let (issuer_session, response) = IssuerSession::new(rng, &request, keys).unwrap();
    let reveal = issuer_session
        .reveal(&OnChainIssuanceRequest::new(&session, &response))
        .unwrap();
    session.unmask(&response, &reveal.signature_mask).unwrap()
}

fn bench_curve<E: Pairing>(c: &mut Criterion, curve: &str)
where
    E: HashToG1,
{
    let mut rng = StdRng::seed_from_u64(0);
    let sig_base = D::generator();
    let keys = IssuerKeypair::<E>::new(&mut rng);

    let mut group = c.benchmark_group(format!("{curve}/issuance"));
    for &n in ISSUANCE {
        let (session, request) = ClientSession::<E, D>::new(&mut rng, n, &sig_base).unwrap();
        let (issuer_session, response) = IssuerSession::new(&mut rng, &request, &keys).unwrap();
        let reveal = issuer_session
            .reveal(&OnChainIssuanceRequest::new(&session, &response))
            .unwrap();

        group.bench_with_input(BenchmarkId::new("client request", n), &n, |b, &n| {
            b.iter(|| ClientSession::<E, D>::new(&mut rng, n, &sig_base).unwrap())
        });
        group.bench_with_input(BenchmarkId::new("issuer sign", n), &n, |b, _| {
            b.iter(|| IssuerSession::new(&mut rng, black_box(&request), &keys).unwrap())
        });
        group.bench_with_input(BenchmarkId::new("client verify response", n), &n, |b, _| {
            b.iter(|| {
                response
                    .verify(&mut rng, black_box(&request), None)
                    .unwrap()
            })
        });
        group.bench_with_input(BenchmarkId::new("client unmask", n), &n, |b, _| {
            b.iter_batched(
                || session.clone(),
                |s| s.unmask(&response, &reveal.signature_mask).unwrap(),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();

    let mut group = c.benchmark_group(format!("{curve}/execute"));
    let reveals: Vec<(Reveal<E>, E::G2Affine, CommitmentToSigMask<E>)> = (0..REVEALS)
        .map(|_| {
            let keys = IssuerKeypair::<E>::new(&mut rng);
            let (session, request) = ClientSession::<E, D>::new(&mut rng, 1, &sig_base).unwrap();
            let (issuer_session, response) = IssuerSession::new(&mut rng, &request, &keys).unwrap();
            let execute = OnChainIssuanceRequest::new(&session, &response);
            let reveal = issuer_session.reveal(&execute).unwrap();
            (reveal, keys.pk, execute.commitment_to_sig_mask)
        })
        .collect();
    let (reveal, pk, commitment) = &reveals[0];
    group.bench_function("reveal verify", |b| {
        b.iter(|| reveal.verify(black_box(pk), commitment, None).unwrap())
    });
    group.bench_function(format!("{REVEALS} reveals verify, RMC"), |b| {
        b.iter(|| {
            RandomizedMultCheckerGuard::<E::G2Affine>::new_using_rng(&mut rng)
                .with_err(Error::InvalidSignatureMask, |rmc| {
                    for (reveal, pk, commitment) in &reveals {
                        reveal.verify(pk, commitment, Some(&mut *rmc))?;
                    }
                    Ok(())
                })
                .unwrap()
        })
    });
    group.finish();

    let mut group = c.benchmark_group(format!("{curve}/spend"));
    for &(n, j) in SPEND {
        let issuers: Vec<IssuerKeypair<E>> = (0..j).map(|_| IssuerKeypair::new(&mut rng)).collect();
        let mut pools: Vec<_> = issuers
            .iter()
            .enumerate()
            .map(|(k, keys)| {
                let count = (n / j + usize::from(k < n % j)) as u32;
                issue(&mut rng, keys, count).0.into_iter()
            })
            .collect();
        let pre: Vec<PreToken<E, D>> = (0..n).map(|i| pools[i % j].next().unwrap()).collect();
        let pk_iss: Vec<E::G2Affine> = (0..n).map(|i| issuers[i % j].pk).collect();
        let payment = Payment::new(&mut rng, &pre, b"bench", &sig_base).unwrap();
        let id = format!("{n} tokens, {j} keys");

        group.bench_function(BenchmarkId::new("client sign", &id), |b| {
            b.iter(|| Payment::new(&mut rng, black_box(&pre), b"bench", &sig_base).unwrap())
        });
        group.bench_function(BenchmarkId::new("verify", &id), |b| {
            b.iter(|| {
                payment
                    .verify(&mut rng, black_box(&pk_iss), b"bench", &sig_base, None)
                    .unwrap()
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group(format!("{curve}/refund"));
    for &n in REFUND {
        let (pre, refund_key) = issue(&mut rng, &keys, n as u32);
        let request = RefundRequest::new(&mut rng, &refund_key, &pre, &sig_base).unwrap();
        let pk_ref = refund_key.keypair.pk;

        group.bench_with_input(BenchmarkId::new("client sign", n), &n, |b, _| {
            b.iter(|| {
                RefundRequest::new(&mut rng, &refund_key, black_box(&pre), &sig_base).unwrap()
            })
        });
        group.bench_with_input(BenchmarkId::new("verify", n), &n, |b, _| {
            b.iter(|| {
                request
                    .verify(&mut rng, black_box(&keys.pk), &pk_ref, &sig_base, None)
                    .unwrap()
            })
        });
    }
    group.finish();

    c.bench_function(&format!("{curve}/hash to G1"), |b| {
        b.iter(|| E::hash_to_g1(black_box(b"bench")))
    });
}

fn protocol(c: &mut Criterion) {
    bench_curve::<ark_bn254::Bn254>(c, "BN254");
    bench_curve::<ark_bls12_381::Bls12_381>(c, "BLS12-381");
}

criterion_group!(benches, protocol);
criterion_main!(benches);
