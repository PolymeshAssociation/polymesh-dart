//! Side-by-side benchmark of the repo's BSGS solver vs the precomputed-table solver in
//! `dock_crypto_utils::solve_discrete_log`, to decide whether to replace the former.
//!
//! Contenders (all on Pallas, the production curve):
//!   - `old_2^21`        : `polymesh_dart_bp::discrete_log::solve_discrete_log_bsgs` (repo default,
//!                          `large_baby_steps` -> 2^21 baby steps, cached per base).
//!   - `new_2^21_cache`  : `solve_discrete_log_bsgs_precomputed_with_table_size` at 2^21, cached.
//!   - `new_2^18_cache`  : same at 2^18 (new-solver default size).
//!   - `new_2^21_given`  : `solve_discrete_log_given_table` over a pre-built 2^21 table (no cache
//!                          lookup) — best-case amortized wallet-scan path.
//!
//! Each cache contender uses its own base: a base's cached table grows to the largest `table_size`
//! ever requested for it, so sharing one would let the 2^21 build enlarge the 2^18 table.

use ark_pallas::{Fr, Projective};
use ark_std::UniformRand;
use ark_std::rand::{RngCore, SeedableRng, rngs::StdRng};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use criterion::{BatchSize, BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::time::{Duration, Instant};

use dock_crypto_utils::solve_discrete_log::{
    BabyStepsTable, solve_discrete_log_bsgs_precomputed_with_table_size,
    solve_discrete_log_bsgs_precomputed_with_table_size_large, solve_discrete_log_given_table,
};
use polymesh_dart_bp::discrete_log::{
    BabyStepsTable as OldBabyStepsTable, MAX_NUM_BABY_STEPS as OLD_TABLE_SIZE,
    solve_discrete_log_bsgs,
};
use polymesh_dart_common::{MAX_ASSET_ID, MAX_BALANCE};

const T16: u64 = 1 << 16;
const T18: u64 = 1 << 18;
const T20: u64 = 1 << 20;
const T21: u64 = 1 << 21;

fn target(base: Projective, dl: u64) -> Projective {
    base * Fr::from(dl)
}

// Warm-cache solve across a DL spread, bound = MAX_BALANCE (48-bit search space).
fn bench_warm_solve(c: &mut Criterion) {
    let base_old = hash_to_pallas(b"cmp", b"old");
    let base_n21 = hash_to_pallas(b"cmp", b"new21");
    let base_n18 = hash_to_pallas(b"cmp", b"new18");
    let base_given_table = hash_to_pallas(b"cmp", b"given");
    let table = BabyStepsTable::<Projective>::new(base_given_table, T21);

    // Warm the per-base caches so the timed region is pure solve.
    let _ = solve_discrete_log_bsgs(MAX_BALANCE, base_old, target(base_old, 3));
    let _ = solve_discrete_log_bsgs_precomputed_with_table_size(
        MAX_BALANCE,
        0,
        T21,
        base_n21,
        target(base_n21, 3),
    );
    let _ = solve_discrete_log_bsgs_precomputed_with_table_size(
        MAX_BALANCE,
        0,
        T18,
        base_n18,
        target(base_n18, 3),
    );

    let mut g = c.benchmark_group("warm_solve/amount_max");
    for dl in [
        0u64, 1, 10, 100, 1_000, 10_000, 65_535, 65_536, 100_000, 1_000_000,
    ] {
        let t_old = target(base_old, dl);
        let t_n21 = target(base_n21, dl);
        let t_n18 = target(base_n18, dl);
        let t_gt = target(base_given_table, dl);

        g.bench_with_input(BenchmarkId::new("old_2^21", dl), &dl, |b, &dl| {
            b.iter(|| {
                assert_eq!(
                    solve_discrete_log_bsgs(MAX_BALANCE, base_old, black_box(t_old)),
                    Some(dl)
                )
            })
        });
        g.bench_with_input(BenchmarkId::new("new_2^21_cache", dl), &dl, |b, &dl| {
            b.iter(|| {
                assert_eq!(
                    solve_discrete_log_bsgs_precomputed_with_table_size(
                        MAX_BALANCE,
                        0,
                        T21,
                        base_n21,
                        black_box(t_n21)
                    ),
                    Some(dl)
                )
            })
        });
        g.bench_with_input(BenchmarkId::new("new_2^18_cache", dl), &dl, |b, &dl| {
            b.iter(|| {
                assert_eq!(
                    solve_discrete_log_bsgs_precomputed_with_table_size(
                        MAX_BALANCE,
                        0,
                        T18,
                        base_n18,
                        black_box(t_n18)
                    ),
                    Some(dl)
                )
            })
        });
        g.bench_with_input(BenchmarkId::new("new_2^21_given", dl), &dl, |b, &dl| {
            b.iter(|| {
                assert_eq!(
                    solve_discrete_log_given_table(
                        &table,
                        base_given_table,
                        0,
                        MAX_BALANCE,
                        black_box(t_gt)
                    ),
                    Some(dl)
                )
            })
        });
    }
    g.finish();
}

// Cold-cache single run: a fresh random base each iteration defeats both caches, so the
// timed region is table build + one solve. `max = MAX_BALANCE`, mid-size DL.
fn bench_cold_solve(c: &mut Criterion) {
    const DL: u64 = 1_234_567;
    let mut g = c.benchmark_group("cold_solve/amount_max");
    g.sample_size(10);

    let mut r_old = StdRng::seed_from_u64(101);
    g.bench_function("old_2^21", |b| {
        b.iter_batched(
            || Projective::rand(&mut r_old),
            |base| {
                assert_eq!(
                    solve_discrete_log_bsgs(MAX_BALANCE, base, target(base, DL)),
                    Some(DL)
                )
            },
            BatchSize::PerIteration,
        )
    });
    let mut r_n21 = StdRng::seed_from_u64(102);
    g.bench_function("new_2^21", |b| {
        b.iter_batched(
            || Projective::rand(&mut r_n21),
            |base| {
                assert_eq!(
                    solve_discrete_log_bsgs_precomputed_with_table_size(
                        MAX_BALANCE,
                        0,
                        T21,
                        base,
                        target(base, DL)
                    ),
                    Some(DL)
                )
            },
            BatchSize::PerIteration,
        )
    });
    let mut r_n18 = StdRng::seed_from_u64(103);
    g.bench_function("new_2^18", |b| {
        b.iter_batched(
            || Projective::rand(&mut r_n18),
            |base| {
                assert_eq!(
                    solve_discrete_log_bsgs_precomputed_with_table_size(
                        MAX_BALANCE,
                        0,
                        T18,
                        base,
                        target(base, DL)
                    ),
                    Some(DL)
                )
            },
            BatchSize::PerIteration,
        )
    });
    g.finish();
}

fn bench_table_build(c: &mut Criterion) {
    let base = hash_to_pallas(b"cmp", b"build");
    let mut g = c.benchmark_group("table_build");
    g.sample_size(10);
    for m in [T16, T18, T20, T21] {
        g.bench_with_input(BenchmarkId::new("new", m), &m, |b, &m| {
            b.iter(|| BabyStepsTable::<Projective>::new(black_box(base), black_box(m)))
        });
    }
    g.bench_function("old", |b| {
        b.iter(|| OldBabyStepsTable::new(black_box(base)).unwrap())
    });
    g.finish();
}

// Large DLs, one per target.
fn large_dl_scan(
    base_old: Projective,
    base_n21: Projective,
    base_n18: Projective,
    base_gt: Projective,
    table_gt: &BabyStepsTable<Projective>,
) {
    const CAP_SECS: f32 = 120.0;
    println!("\n=== (D) large-DL single run (max = MAX_BALANCE), cap {CAP_SECS:.0}s/solve ===");
    let dls: Vec<(u64, &str)> = vec![
        (1_000_000, "10^6"),
        (10_000_000, "10^7"),
        (100_000_000, "10^8"),
        ((1u64 << 32) - 1, "2^32-1"),
        (1u64 << 32, "2^32"),
        (1u64 << 36, "2^36"),
        (1u64 << 40, "2^40"),
        (1u64 << 44, "2^44"),
        (1u64 << 47, "2^47"),
        (MAX_BALANCE, "MAX_BALANCE"),
    ];
    let time = |f: &dyn Fn() -> Option<u64>, dl: u64| -> (f32, bool) {
        let s = Instant::now();
        let v = f();
        let secs = s.elapsed().as_secs_f32();
        (secs, v == Some(dl))
    };
    println!(
        "{:>12} | {:>10} {:>10} {:>10} {:>10} {:>10}",
        "dl", "old_2^21", "new_2^21", "new_2^18", "given_2^21", "new_2^21_L"
    );
    for (dl, label) in dls {
        if dl > MAX_BALANCE {
            continue;
        }
        let (o, ok_o) = time(
            &|| solve_discrete_log_bsgs(MAX_BALANCE, base_old, target(base_old, dl)),
            dl,
        );
        let (a, ok_a) = time(
            &|| {
                solve_discrete_log_bsgs_precomputed_with_table_size(
                    MAX_BALANCE,
                    0,
                    T21,
                    base_n21,
                    target(base_n21, dl),
                )
            },
            dl,
        );
        let (b, ok_b) = time(
            &|| {
                solve_discrete_log_bsgs_precomputed_with_table_size(
                    MAX_BALANCE,
                    0,
                    T18,
                    base_n18,
                    target(base_n18, dl),
                )
            },
            dl,
        );
        let (g, ok_g) = time(
            &|| {
                solve_discrete_log_given_table(
                    table_gt,
                    base_gt,
                    0,
                    MAX_BALANCE,
                    target(base_gt, dl),
                )
            },
            dl,
        );
        let (l, ok_l) = time(
            &|| {
                solve_discrete_log_bsgs_precomputed_with_table_size_large(
                    MAX_BALANCE,
                    0,
                    T21,
                    base_n21,
                    target(base_n21, dl),
                )
            },
            dl,
        );
        assert!(
            ok_o && ok_a && ok_b && ok_g && ok_l,
            "wrong result at dl={label}"
        );
        println!(
            "{:>12} | {:>9.3}s {:>9.3}s {:>9.3}s {:>9.3}s {:>9.3}s",
            label, o, a, b, g, l
        );
        if o.max(a).max(b).max(g).max(l) > CAP_SECS {
            println!("(cap hit at dl={label}, stopping)");
            break;
        }
    }
}

// N solves with a fixed base and random DLs, mirroring a wallet decrypting many legs.
// Reported for small amounts (< 2^20) and big (< 2^32).
fn fixed_table_scan(
    base_old: Projective,
    base_n21: Projective,
    base_n18: Projective,
    base_gt: Projective,
    table_gt: &BabyStepsTable<Projective>,
) {
    const N: usize = 1_000;
    println!("\n=== (E) amortized scan, N={N} solves, fixed base (max = MAX_BALANCE) ===");

    // Warm (build+cache) the tables before timing.
    let _ = solve_discrete_log_bsgs(MAX_BALANCE, base_old, target(base_old, 100));
    let _ = solve_discrete_log_bsgs_precomputed_with_table_size(
        MAX_BALANCE,
        0,
        T21,
        base_n21,
        target(base_n21, 100),
    );
    let _ = solve_discrete_log_bsgs_precomputed_with_table_size(
        MAX_BALANCE,
        0,
        T18,
        base_n18,
        target(base_n18, 100),
    );

    for (label, bound) in [("small (<2^20)", 1u64 << 20), ("big (<2^32)", 1u64 << 32)] {
        let mut rng = StdRng::seed_from_u64(7);
        let dls: Vec<u64> = (0..N).map(|_| rng.next_u64() % bound).collect();
        let t_old: Vec<_> = dls.iter().map(|&d| target(base_old, d)).collect();
        let t_n21: Vec<_> = dls.iter().map(|&d| target(base_n21, d)).collect();
        let t_n18: Vec<_> = dls.iter().map(|&d| target(base_n18, d)).collect();
        let t_gt: Vec<_> = dls.iter().map(|&d| target(base_gt, d)).collect();

        let scan = |targets: &[Projective], f: &dyn Fn(&Projective) -> Option<u64>| -> Duration {
            let s = Instant::now();
            for (i, t) in targets.iter().enumerate() {
                assert_eq!(f(t), Some(dls[i]));
            }
            s.elapsed()
        };
        let d_old = scan(&t_old, &|t| {
            solve_discrete_log_bsgs(MAX_BALANCE, base_old, *t)
        });
        let d_n21 = scan(&t_n21, &|t| {
            solve_discrete_log_bsgs_precomputed_with_table_size(MAX_BALANCE, 0, T21, base_n21, *t)
        });
        let d_n18 = scan(&t_n18, &|t| {
            solve_discrete_log_bsgs_precomputed_with_table_size(MAX_BALANCE, 0, T18, base_n18, *t)
        });
        let d_gt = scan(&t_gt, &|t| {
            solve_discrete_log_given_table(table_gt, base_gt, 0, MAX_BALANCE, *t)
        });
        println!(
            "  {label:>14}: old_2^21 {d_old:>10.3?} | new_2^21 {d_n21:>10.3?} | new_2^18 {d_n18:>10.3?} | given_2^21 {d_gt:>10.3?}"
        );
    }
}

fn report_memory() {
    println!("\n=== (C) table memory ===");
    println!(
        "  old: {} entries, key = 32-byte compressed point + u32 value",
        OLD_TABLE_SIZE
    );
    for m in [T16, T18, T20, T21] {
        println!(
            "  new(m={}): {} entries, key = ~32-byte x-coordinate + u32 value",
            m, m
        );
    }
    println!(
        "  asset-id space max = {} ({}-bit), amount space max = {} (48-bit)",
        MAX_ASSET_ID, 32, MAX_BALANCE
    );
}

fn bench_manual_sections(_c: &mut Criterion) {
    let base_old = hash_to_pallas(b"man", b"old");
    let base_n21 = hash_to_pallas(b"man", b"new21");
    let base_n18 = hash_to_pallas(b"man", b"new18");
    let base_gt = hash_to_pallas(b"man", b"given");
    let table_gt = BabyStepsTable::<Projective>::new(base_gt, T21);

    report_memory();
    fixed_table_scan(base_old, base_n21, base_n18, base_gt, &table_gt);
    large_dl_scan(base_old, base_n21, base_n18, base_gt, &table_gt);
}

criterion_group!(
    benches,
    bench_warm_solve,
    bench_cold_solve,
    bench_table_build,
    bench_manual_sections
);
criterion_main!(benches);
