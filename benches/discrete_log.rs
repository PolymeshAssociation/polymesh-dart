use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use ark_pallas::Fr;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use polymesh_dart_bp::discrete_log::solve_discrete_log_bsgs;
use polymesh_dart_common::MAX_BALANCE;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

fn discrete_log_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Discrete Log BSGS Alt");

    let enc_gen = hash_to_pallas(b"bench", b"enc-gen");

    // Warm up the Baby Steps cache
    {
        let amount = 1_000u64;
        let enc_amount = enc_gen * Fr::from(amount);

        let value = solve_discrete_log_bsgs(MAX_BALANCE, enc_gen, black_box(enc_amount))
            .expect("Failed to solve discrete log for base");
        assert_eq!(amount, value);
    }

    for i in 2..6 {
        let amount = (10u64).pow(i);
        let enc_amount = enc_gen * Fr::from(amount);

        group.bench_with_input(
            BenchmarkId::new("discrete_log", amount),
            &enc_amount,
            |b, enc_amount| {
                b.iter(|| {
                    let value =
                        solve_discrete_log_bsgs(MAX_BALANCE, enc_gen, black_box(*enc_amount))
                            .expect("Failed to solve discrete log for base");
                    assert_eq!(amount, value);
                })
            },
        );
    }

    eprintln!("--- Verifying discrete log correctness for amounts 0 to 50,000,000 ---");
    (0..50u64).into_par_iter().for_each(|chunk_idx| {
        let start = chunk_idx * 1_000_000;
        let end = start + 1_000_000;
        for amount in start..end {
            let enc_amount = enc_gen * Fr::from(amount);

            let value = solve_discrete_log_bsgs(MAX_BALANCE, enc_gen, black_box(enc_amount))
                .expect("Failed to solve discrete log for base");
            assert_eq!(amount, value);
        }
        eprintln!("Finished verifying amounts {} to {}", start, end - 1);
    });

    const MAX_DISCRETE_LOG_TIME_SECS: f32 = 300.0;
    let legs: Vec<_> = vec![
        (0u64, "0"),
        (1u64, "1"),
        (10u64, "10"),
        (100u64, "100"),
        (1_000u64, "1,000"),
        (10_000u64, "10,000"),
        (65_535u64, "65,535"),
        (65_536u64, "65,536"),
        (65_537u64, "65,537"),
        (100_000u64, "100,000"),
        (131_070u64, "131,070"),
        (131_072u64, "131,072"),
        (1_000_000u64, "1,000,000"),
        (10_000_000u64, "10,000,000"),
        (100_000_000u64, "100,000,000"),
        (1_000_000_000u64, "1,000,000,000"),
        (10_000_000_000u64, "10,000,000,000"),
        (100_000_000_000u64, "100,000,000,000"),
        (1_000_000_000_000u64, "1,000,000,000,000"),
        (10_000_000_000_000u64, "10,000,000,000,000"),
        //(100_000_000_000_000u64, "100,000,000,000,000"),
        (2u64.pow(40), "2^40"),
        (2u64.pow(41), "2^41"),
        (2u64.pow(42), "2^42"),
        (2u64.pow(43), "2^43"),
        (2u64.pow(44), "2^44"),
        (2u64.pow(45), "2^45"),
        (2u64.pow(46), "2^46"),
        (2u64.pow(47), "2^47"),
        (2u64.pow(48) - 2, "2^48 - 2"),
    ]
    .into_iter()
    .filter_map(|(amount, s_amount)| {
        if amount >= MAX_BALANCE {
            return None;
        }
        eprintln!("Preparing for amount {}", s_amount);
        let enc_amount = enc_gen * Fr::from(amount);

        Some((amount, enc_amount, format!("{:>19}", s_amount)))
    })
    .collect();
    for (amount, enc_amount, s_amount) in &legs {
        let now = std::time::Instant::now();
        print!("--- time to discrete_log  {}: ", s_amount);
        let value = solve_discrete_log_bsgs(MAX_BALANCE, enc_gen, *enc_amount)
            .expect("Failed to solve discrete log for base");
        assert_eq!(*amount, value);
        let secs = now.elapsed().as_secs_f32();
        println!("{:.3?} secs", secs);
        // Stop if elapsed time above threshold.
        if secs > MAX_DISCRETE_LOG_TIME_SECS {
            println!(
                "Discrete log time exceeded threshold of {:.1} secs, stopping further tests.",
                MAX_DISCRETE_LOG_TIME_SECS
            );
            break;
        }
    }
}

criterion_group!(discrete_log_benches, discrete_log_benchmark);
criterion_main!(discrete_log_benches);
