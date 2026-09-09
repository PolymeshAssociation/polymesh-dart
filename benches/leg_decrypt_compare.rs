//! Leg-decryption discrete-log comparison: dart's BSGS solver vs this repo's precomputed-table solver
//! (`dock_crypto_utils::solve_discrete_log`), on the exact curve-group discrete log a leg decryption
//! solves to recover the amount.
//!
//! A sender/receiver decrypt recovers the amount as `amount = dlog_{enc_gen}(amount_pt)`, where
//! `amount_pt = enc_gen * amount` is the ElGamal-decrypted point and `enc_gen` is the leg amount
//! generator (`dart_gens().leg_asset_value_gen()`, on Pallas). The ElGamal step that produces
//! `amount_pt` is one scalar-mul + one subtraction (see `Leg::decrypt_element_with_sk_inv`) — shared by
//! both solvers and cheap — so the amount discrete log is the dominant and only differing cost of a
//! decryption. This bench isolates it and feeds both solvers the identical `(enc_gen, enc_gen * amount)`.
//!
//! Contenders (Pallas, cached per base):
//!   - `dart`      : `polymesh_dart_bp::discrete_log::solve_discrete_log_bsgs` (production, `large_baby_steps`
//!                   -> 2^21 baby steps).
//!   - `new_2^21`  : `dock_crypto_utils` `solve_discrete_log_bsgs_precomputed_with_table_size` at 2^21 (same
//!                   table size, negation map + direct fast path).
//!

use ark_ec::AffineRepr;
use ark_pallas::{Fr, Projective};
use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::time::{Duration, Instant};

use dock_crypto_utils::solve_discrete_log::solve_discrete_log_bsgs_precomputed_with_table_size;
use polymesh_dart::*;
use polymesh_dart_bp::discrete_log::solve_discrete_log_bsgs;
use polymesh_dart_bp::leg::LegEncConfig;

const T21: u64 = 1 << 21;

// The leg amount-encryption generator, as a projective point (base of the amount discrete log).
fn enc_gen() -> Projective {
    dart_gens().leg_asset_value_gen().into_group()
}

// The ElGamal-decrypted amount point `enc_gen * amount`, i.e. the exact target the decryption solves.
fn amount_pt(g: Projective, amount: u64) -> Projective {
    g * Fr::from(amount)
}

fn dart_solve(g: Projective, pt: Projective) -> Option<u64> {
    solve_discrete_log_bsgs::<Projective>(MAX_BALANCE, g, pt)
}

fn new_solve(g: Projective, pt: Projective) -> Option<u64> {
    solve_discrete_log_bsgs_precomputed_with_table_size::<Projective>(MAX_BALANCE, 0, T21, g, pt)
}

// Full leg decryption (dart) next to the amount dl-solve alone (dart, new). The full decrypt uses
// dart's solver internally; comparing it against `amount_dl/dart` shows the ElGamal + asset-id overhead is
// a small constant, so a decryption's latency is essentially its amount dl-solve.
fn bench_decrypt_vs_solve(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let sender_keys = AccountKeys::rand(&mut rng).expect("sender keys");
    let sender = sender_keys.public_keys();
    let receiver_keys = AccountKeys::rand(&mut rng).expect("receiver keys");
    let receiver = receiver_keys.public_keys();
    let asset_id = 0;
    let g = enc_gen();

    // Warm both per-base caches so the timed region is pure solve.
    let _ = dart_solve(g, amount_pt(g, 3));
    let _ = new_solve(g, amount_pt(g, 3));

    let mut group = c.benchmark_group("leg_decrypt_vs_solve");
    group.sample_size(10);

    for amount in [
        1_000u64,
        100_000,
        1_000_000,
        2_000_000,
        3_000_000,
        100_000_000,
    ] {
        let leg = Leg::new(sender.enc, receiver.enc, asset_id, amount).expect("leg");
        let (_, leg_enc, _) = leg
            .encrypt(&mut rng, LegEncConfig::default(), vec![], vec![], vec![])
            .expect("encrypt");
        let pt = amount_pt(g, amount);

        group.bench_with_input(
            BenchmarkId::new("decrypt_full/dart", amount),
            &amount,
            |b, _| {
                b.iter(|| {
                    let leg = black_box(&leg_enc)
                        .decrypt(LegRole::sender(), &sender_keys)
                        .expect("decrypt");
                    assert_eq!(amount, leg.amount);
                })
            },
        );
        group.bench_with_input(
            BenchmarkId::new("amount_dl/dart", amount),
            &amount,
            |b, _| b.iter(|| assert_eq!(dart_solve(g, black_box(pt)), Some(amount))),
        );
        group.bench_with_input(
            BenchmarkId::new("amount_dl/new_2^21", amount),
            &amount,
            |b, _| b.iter(|| assert_eq!(new_solve(g, black_box(pt)), Some(amount))),
        );
    }
    group.finish();
}

// Single run amount dl-solve across the leg amounts, up to `MAX_BALANCE`.
fn single_run(_c: &mut Criterion) {
    const CAP_SECS: f32 = 8.0;
    let g = enc_gen();

    // Warm caches (dl != 0/1 so no early-return shortcut is timed).
    let _ = dart_solve(g, amount_pt(g, 100));
    let _ = new_solve(g, amount_pt(g, 100));

    let amounts: Vec<(u64, &str)> = vec![
        (10, "10"),
        (100, "100"),
        (1_000, "1,000"),
        (10_000, "10,000"),
        (65_535, "65,535"),
        (100_000, "100,000"),
        (1_000_000, "1,000,000"),
        (2_097_152, "2^21"),
        (2_097_153, "2^21 + 1"),
        (10_000_000, "10,000,000"),
        (100_000_000, "100,000,000"),
        (1_000_000_000, "1,000,000,000"),
        (10_000_000_000, "10,000,000,000"),
        (1u64 << 32, "2^32"),
        (1u64 << 36, "2^36"),
        (1u64 << 40, "2^40"),
        (1u64 << 44, "2^44"),
        (1u64 << 47, "2^47"),
        (MAX_BALANCE, "MAX_BALANCE"),
    ];

    let time = |f: &dyn Fn() -> Option<u64>, amount: u64| -> (f32, bool) {
        let s = Instant::now();
        let v = f();
        (s.elapsed().as_secs_f32(), v == Some(amount))
    };

    println!("\n=== (B) amount dl-solve, single run (max = MAX_BALANCE), cap {CAP_SECS:.0}s ===");
    println!("{:>18} | {:>12} {:>12}", "amount", "dart", "new_2^21");
    for (amount, label) in amounts {
        if amount >= MAX_BALANCE && label != "MAX_BALANCE" {
            continue;
        }
        let pt = amount_pt(g, amount);
        let (dt, ok_d) = time(&|| dart_solve(g, pt), amount);
        let (nt, ok_n) = time(&|| new_solve(g, pt), amount);
        assert!(ok_d && ok_n, "wrong result at amount {label}");
        println!("{:>18} | {:>11.4}s {:>11.4}s", label, dt, nt);
        if dt.max(nt) > CAP_SECS {
            println!("(cap hit at amount {label}, stopping sweep)");
            break;
        }
    }
}

criterion_group!(benches, bench_decrypt_vs_solve, single_run);
criterion_main!(benches);
