use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use std::hint::black_box;

use polymesh_dart::*;

fn decrypt_benchmark(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let sender_keys = AccountKeys::rand(&mut rng).expect("Failed to generate issuer keys");
    let sender = sender_keys.public_keys();
    let receiver_keys = AccountKeys::rand(&mut rng).expect("Failed to generate investor keys");
    let receiver = receiver_keys.public_keys();

    let asset_id = 0;

    let mut group = c.benchmark_group("Leg decryption");

    for i in 2..6 {
        let amount = (10 as Balance).pow(i);
        let leg =
            Leg::new(sender.acct, receiver.acct, asset_id, amount).expect("Failed to create leg");
        let (_leg, leg_enc, _leg_enc_rand) = leg
            .encrypt(&mut rng, sender.enc, receiver.enc, &[])
            .expect("Failed to encrypt leg");

        group.bench_with_input(
            BenchmarkId::new("decrypt", amount),
            &leg_enc,
            |b, leg_enc| {
                b.iter(|| {
                    let leg = black_box(leg_enc)
                        .decrypt(LegRole::Sender, &sender_keys)
                        .expect("Failed to decrypt leg");
                    assert_eq!(amount, leg.amount);
                })
            },
        );
    }

    const MAX_DECRYPT_TIME_SECS: f32 = 4.0;
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
        (2u64.pow(48) - 1, "2^48 - 1"),
    ]
    .into_iter()
    .filter_map(|(amount, s_amount)| {
        if amount >= MAX_BALANCE {
            return None;
        }
        eprintln!("Preparing leg for amount {}", s_amount);
        let leg =
            Leg::new(sender.acct, receiver.acct, asset_id, amount).expect("Failed to create leg");
        let (_leg, leg_enc, _leg_enc_rand) = leg
            .encrypt(&mut rng, sender.enc, receiver.enc, &[])
            .expect("Failed to encrypt leg");

        Some((amount, leg_enc, format!("{:>19}", s_amount)))
    })
    .collect();
    for (amount, leg_enc, s_amount) in &legs {
        let now = std::time::Instant::now();
        print!("--- time to decrypt       {}: ", s_amount);
        let leg = leg_enc
            .decrypt(LegRole::Sender, &sender_keys)
            .expect("Failed to decrypt leg");
        assert_eq!(*amount, leg.amount);
        let secs = now.elapsed().as_secs_f32();
        println!("{:.3?} secs", secs);
        // Stop if elapsed time above threshold.
        if secs > MAX_DECRYPT_TIME_SECS {
            println!(
                "Decryption time exceeded threshold of {:.1} secs, stopping further tests.",
                MAX_DECRYPT_TIME_SECS
            );
            break;
        }
    }
}

criterion_group!(decrypt_benches, decrypt_benchmark);
criterion_main!(decrypt_benches);
