use std::collections::BTreeMap;
use std::hint::black_box;

use codec::{Decode, Encode};
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

use polymesh_dart::*;

type Registry = BTreeMap<BatIssuerKeyId, BatIssuerPublicKey>;

const ISSUANCE: &[u32] = &[1, 10, 100];
/// `(tokens, issuer keys)`.
const SPEND: &[(usize, u32)] = &[(1, 1), (8, 1), (8, 8), (32, 1), (32, 32)];
const REFUND: &[u32] = &[1, 10, 100];

fn registry(n: u32) -> (Vec<BatIssuerKeys>, Registry) {
    let keys: Vec<BatIssuerKeys> = (0..n)
        .map(|id| BatIssuerKeys::new_with_seed(&id.to_le_bytes()))
        .collect();
    let lookup = keys
        .iter()
        .enumerate()
        .map(|(id, k)| (id as BatIssuerKeyId, k.public_key().unwrap()))
        .collect();
    (keys, lookup)
}

fn buy(
    rng: &mut ChaCha20Rng,
    keys: &BatIssuerKeys,
    issuer: BatIssuerKeyId,
    count: u32,
) -> (Vec<BatPreToken>, BatRefundKey, BatOnChainIssuanceRequest) {
    let (session, request) = BatClientSession::new(rng, issuer, count).unwrap();
    let (issuer_session, response) = keys.sign(rng, issuer, &request).unwrap();
    let execute = session.on_chain_issue_request(rng, &response).unwrap();
    let reveal = issuer_session.reveal(&execute).unwrap();
    let (tokens, refund_key) = session.unmask(&response, &reveal).unwrap();
    (tokens, refund_key, execute)
}

fn bat_benchmark(c: &mut Criterion) {
    let mut rng = ChaCha20Rng::from_seed([42; 32]);
    let (keys, lookup) = registry(1);

    let mut group = c.benchmark_group("BAT issuance");
    for &n in ISSUANCE {
        let (session, request) = BatClientSession::new(&mut rng, 0, n).unwrap();
        let (issuer_session, response) = keys[0].sign(&mut rng, 0, &request).unwrap();
        let execute = session.on_chain_issue_request(&mut rng, &response).unwrap();
        let reveal = issuer_session.clone().reveal(&execute).unwrap();

        group.bench_with_input(BenchmarkId::new("client request", n), &n, |b, &n| {
            b.iter(|| BatClientSession::new(&mut rng, 0, n).unwrap())
        });
        group.bench_with_input(BenchmarkId::new("issuer sign", n), &n, |b, _| {
            b.iter(|| keys[0].sign(&mut rng, 0, black_box(&request)).unwrap())
        });
        group.bench_with_input(BenchmarkId::new("client execute request", n), &n, |b, _| {
            b.iter(|| {
                session
                    .on_chain_issue_request(&mut rng, black_box(&response))
                    .unwrap()
            })
        });
        group.bench_with_input(BenchmarkId::new("issuer reveal", n), &n, |b, _| {
            b.iter_batched(
                || issuer_session.clone(),
                |s| s.reveal(&execute).unwrap(),
                BatchSize::SmallInput,
            )
        });
        group.bench_with_input(BenchmarkId::new("client unmask", n), &n, |b, _| {
            b.iter_batched(
                || session.clone(),
                |s| s.unmask(&response, &reveal).unwrap(),
                BatchSize::SmallInput,
            )
        });
    }
    group.finish();

    let (session, request) = BatClientSession::new(&mut rng, 0, 1).unwrap();
    let (issuer_session, response) = keys[0].sign(&mut rng, 0, &request).unwrap();
    let execute = session.on_chain_issue_request(&mut rng, &response).unwrap();
    let reveal = issuer_session.reveal(&execute).unwrap();
    let mut group = c.benchmark_group("BAT execute");
    group.bench_function("issuer key validate", |b| {
        b.iter(|| lookup[&0].validate().unwrap())
    });
    group.bench_function("execute request verify", |b| {
        b.iter(|| black_box(&execute).verify::<PolymeshLimits>().unwrap())
    });
    group.bench_function("reveal verify", |b| {
        b.iter(|| {
            black_box(&reveal)
                .verify(&lookup[&0], &execute.commitment_to_sig_mask)
                .unwrap()
        })
    });
    group.finish();

    let mut group = c.benchmark_group("BAT fee payment");
    for &(n, j) in SPEND {
        let (keys, lookup) = registry(j);
        let mut tokens: Vec<Vec<BatPreToken>> = keys
            .iter()
            .enumerate()
            .map(|(k, keys)| {
                let count = n as u32 / j + u32::from((k as u32) < n as u32 % j);
                buy(&mut rng, keys, k as BatIssuerKeyId, count).0
            })
            .collect();
        let spent: Vec<BatPreToken> = (0..n)
            .map(|i| tokens[i % j as usize].pop().unwrap())
            .collect();
        let batch = BatFeePaymentWithBatchedProofs::<PolymeshLimits>::new(
            &mut rng,
            &spent,
            BatchedProofs::new(),
        )
        .unwrap();
        let encoded = batch.encode();
        let id = format!("{n} tokens, {j} keys");

        group.bench_function(BenchmarkId::new("client sign", &id), |b| {
            b.iter(|| {
                BatFeePaymentWithBatchedProofs::<PolymeshLimits>::new(
                    &mut rng,
                    black_box(&spent),
                    BatchedProofs::new(),
                )
                .unwrap()
            })
        });
        group.bench_function(BenchmarkId::new("decode and verify", &id), |b| {
            b.iter(|| {
                BatFeePaymentWithBatchedProofs::<PolymeshLimits>::decode(&mut &encoded[..])
                    .unwrap()
                    .verify_fee_payment(&mut rng, &lookup)
                    .unwrap()
            })
        });
    }
    group.finish();

    let mut group = c.benchmark_group("BAT refund");
    for &n in REFUND {
        let (tokens, refund_key, execute) = buy(&mut rng, &keys[0], 0, n);
        let refund =
            BatRefundRequest::<PolymeshLimits>::new(&mut rng, &refund_key, &tokens).unwrap();

        group.bench_with_input(BenchmarkId::new("client sign", n), &n, |b, _| {
            b.iter(|| {
                BatRefundRequest::<PolymeshLimits>::new(&mut rng, &refund_key, black_box(&tokens))
                    .unwrap()
            })
        });
        group.bench_with_input(BenchmarkId::new("verify", n), &n, |b, _| {
            b.iter(|| {
                black_box(&refund)
                    .verify(&mut rng, &lookup[&0], &execute.pk_ref)
                    .unwrap()
            })
        });
    }
    group.finish();
}

criterion_group!(benches, bat_benchmark);
criterion_main!(benches);
