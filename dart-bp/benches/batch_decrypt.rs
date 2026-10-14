//! Batch trial decryption for Twisted ElGamal ciphertexts sharing one `sk`, and the two-round leg
//! scan built on it. Measures the shared-scalar GLV ladder against per-item point decryption, the
//! discrete log per recovered value against the same solve on a point with no log in range, a full
//! `batch_decrypt_legs` scan against per-leg decryption, and the two-round scan's ladder columns
//! against those a single fused ladder would need.

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, UniformRand};
use ark_pallas::{Affine as PallasA, Fr, PallasConfig, Projective};
use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;
use std::time::Instant;

use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use polymesh_dart_bp::batch_decrypt::batch_decrypt_points;
use polymesh_dart_bp::discrete_log::{MAX_NUM_BABY_STEPS, solve_discrete_log_precomputed};
use polymesh_dart_bp::keys::keygen_enc;
use polymesh_dart_bp::leg::{Leg, LegEncConfig, LegEncryption, PartyVisibility};
use polymesh_dart_common::{AssetId, Balance, MAX_ASSET_ID, MAX_BALANCE};
use rand_core::CryptoRngCore;

/// Amount width that keeps every discrete log inside the solver's first window, so a scan's cost is
/// the ladder rather than the solver.
const SMALL_AMOUNT_BITS: u32 = 11;

/// Legs per row of the large-amount sweep. The per-leg side pays a flat per-value solve cost there,
/// so this is what sets that benchmark's runtime.
const LARGE_AMOUNT_LEGS: usize = 64;

/// Amount widths for the large-amount sweep. 24 still lands in the solver's first chunk; 32 and 40
/// do not. Above 40 the per-leg side runs into tens of seconds per repetition.
const LARGE_AMOUNT_BITS: [u32; 3] = [24, 32, 40];

struct Setup {
    legs: Vec<LegEncryption<PallasA>>,
    sk: Fr,
    pk: PallasA,
    enc_gen: PallasA,
}

/// `n` legs of which `participant` carry the scanning party as sender or receiver and the rest are
/// between two other parties.
fn build_legs(
    n: usize,
    participant: usize,
    reveal_asset_id: bool,
    amount_bits: u32,
    rng: &mut impl CryptoRngCore,
) -> Setup {
    let label = b"batch-decrypt-bench";
    let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
    let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

    let (sk, pk) = keygen_enc(rng, enc_key_gen);
    let (_, other) = keygen_enc(rng, enc_key_gen);
    let (_, third) = keygen_enc(rng, enc_key_gen);

    let lo = 1u64 << (amount_bits - 1);
    let legs = (0..n)
        .map(|i| {
            let (pk_s, pk_r) = if i < participant {
                if i % 2 == 0 {
                    (pk.0, other.0)
                } else {
                    (other.0, pk.0)
                }
            } else {
                (other.0, third.0)
            };
            let leg = Leg::new(
                pk_s,
                pk_r,
                (lo + i as u64 * lo / n as u64) as Balance,
                (i % 16) as AssetId,
                vec![],
                vec![],
                vec![],
            )
            .unwrap();
            leg.encrypt(
                rng,
                LegEncConfig {
                    visibility: PartyVisibility::FullVisibility,
                    reveal_asset_id,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap()
            .0
        })
        .collect();

    Setup {
        legs,
        sk: sk.0,
        pk: pk.0,
        enc_gen,
    }
}

fn scan_legs_role_and_amount_separately(s: &Setup) -> usize {
    s.legs
        .iter()
        .filter_map(|leg| {
            let role = leg.identify_role(&s.sk, s.pk).unwrap()?;
            LegEncryption::batch_decrypt_values(
                &[(leg, role)],
                &s.sk,
                s.enc_gen,
                MAX_ASSET_ID,
                MAX_BALANCE,
            )
            .ok()
        })
        .count()
}

fn scan_legs_role_and_amount_together(s: &Setup) -> usize {
    LegEncryption::batch_decrypt_legs(&s.legs, &s.sk, s.pk, s.enc_gen, MAX_ASSET_ID, MAX_BALANCE)
        .unwrap()
        .len()
}

/// Whether criterion's benchmark filter selects `section`. `criterion_group!` calls every function
/// it registers, and the filter only reaches `bench_function` ids, so the printed tables have to
/// check it themselves. The filter is the first bare argument; an option value that happens to be
/// bare (`--sample-size 10`) is read as one and suppresses the tables, which costs only output.
fn selected(section: &str) -> bool {
    std::env::args()
        .skip(1)
        .find(|a| !a.starts_with('-'))
        .is_none_or(|filter| section.contains(&filter))
}

fn time<T>(reps: usize, mut f: impl FnMut() -> T) -> f64 {
    let t = Instant::now();
    for _ in 0..reps {
        black_box(f());
    }
    t.elapsed().as_secs_f64() / reps as f64
}

/// Builds `n` amount ciphertexts under one `sk`: `pk = sk * enc_key_gen`, and for each leg
/// `eph_pk = r * pk`, `ct = enc_key_gen * r + enc_gen * amount`, so `ct - sk^{-1} * eph_pk = enc_gen * amount`.
fn build_ciphertexts(
    n: usize,
    rng: &mut impl rand::Rng,
) -> (Vec<PallasA>, Vec<PallasA>, Fr, PallasA, Vec<u64>) {
    let enc_key_gen = PallasA::rand(rng);
    let enc_gen = PallasA::rand(rng);
    let sk = Fr::rand(rng);
    let pk = (enc_key_gen * sk).into_affine();

    let mut eph_pks = Vec::with_capacity(n);
    let mut cts = Vec::with_capacity(n);
    let mut amounts = Vec::with_capacity(n);
    for _ in 0..n {
        let r = Fr::rand(rng);
        let amount = (rng.next_u32() % 100_000) as u64;
        eph_pks.push((pk * r).into_affine());
        cts.push((enc_key_gen * r + enc_gen * Fr::from(amount)).into_affine());
        amounts.push(amount);
    }
    (eph_pks, cts, sk, enc_gen, amounts)
}

/// `ct_i - sk^{-1} * eph_pk_i` one leg at a time.
fn per_item_points(eph_pks: &[PallasA], cts: &[PallasA], sk: &Fr) -> Vec<PallasA> {
    let sk_inv = sk.inverse().unwrap();
    let pts: Vec<Projective> = cts
        .iter()
        .zip(eph_pks)
        .map(|(ct, eph)| ct.into_group() - *eph * sk_inv)
        .collect();
    Projective::normalize_batch(&pts)
}

/// The ladder columns a fused, speculative single-ladder scan would need: both parties' ephemeral
/// keys for the amount and the asset-id, because neither ciphertext can be opened without first
/// knowing which side of the leg the scanner is on.
fn speculative_columns(s: &Setup) -> (Vec<PallasA>, Vec<PallasA>) {
    let mut eph_pks = Vec::with_capacity(6 * s.legs.len());
    let mut cts = Vec::with_capacity(6 * s.legs.len());
    for leg in &s.legs {
        for is_sender in [true, false] {
            let (eph, ct) = leg.eph_pk_and_ct_participant(is_sender);
            eph_pks.push(eph);
            cts.push(ct);
            eph_pks.push(leg.eph_pk_amount(is_sender));
            cts.push(leg.ct_amount());
            if let (Some(eph), Some(ct)) =
                (leg.eph_pk_asset_id(is_sender), leg.asset_id_ciphertext())
            {
                eph_pks.push(eph);
                cts.push(ct);
            }
        }
    }
    (eph_pks, cts)
}

fn eph_pks_and_cts_role_and_amounts(
    s: &Setup,
) -> ((Vec<PallasA>, Vec<PallasA>), (Vec<PallasA>, Vec<PallasA>)) {
    let n = s.legs.len();
    let mut role_eph = Vec::with_capacity(2 * n);
    let mut role_cts = Vec::with_capacity(2 * n);
    for leg in &s.legs {
        for is_sender in [true, false] {
            let (eph, ct) = leg.eph_pk_and_ct_participant(is_sender);
            role_eph.push(eph);
            role_cts.push(ct);
        }
    }
    let roles = LegEncryption::batch_identify_role(&s.legs, &s.sk, s.pk).unwrap();
    let mut amount_eph = Vec::with_capacity(2 * n);
    let mut amount_cts = Vec::with_capacity(2 * n);
    for (leg, role) in s.legs.iter().zip(&roles) {
        let Some(role) = role else { continue };
        let is_sender = role.is_sender();
        amount_eph.push(leg.eph_pk_amount(is_sender));
        amount_cts.push(leg.ct_amount());
        if let (Some(eph), Some(ct)) = (leg.eph_pk_asset_id(is_sender), leg.asset_id_ciphertext()) {
            amount_eph.push(eph);
            amount_cts.push(ct);
        }
    }
    ((role_eph, role_cts), (amount_eph, amount_cts))
}

fn bench_batch_decrypt(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    if selected("batch_decrypt") {
        // Correctness + a printed per-item-vs-batch ratio table (BATCH_AFFINE_MIN_POINTS = 32 in the
        // fork, so the shared-inversion affine ladder engages at n >= 32).
        println!(
            "\n=== batch trial decryption: point step (ct - sk^-1*eph_pk), Pallas ===\n{:>7}  {:>12}  {:>12}  {:>8}",
            "n", "per-item", "batch", "speedup"
        );
        for &n in &[8usize, 32, 128, 512, 1024, 4096] {
            let (eph_pks, cts, sk, enc_gen, amounts) = build_ciphertexts(n, &mut rng);

            let per = per_item_points(&eph_pks, &cts, &sk);
            let bat = batch_decrypt_points::<PallasConfig>(&eph_pks, &cts, &sk).unwrap();
            assert_eq!(per, bat);
            for (pt, amount) in bat.iter().zip(&amounts) {
                assert_eq!(*pt, (enc_gen * Fr::from(*amount)).into_affine());
            }

            let reps = (200_000 / n).max(5);
            let per_t = time(reps, || per_item_points(&eph_pks, &cts, &sk));
            let bat_t = time(reps, || {
                batch_decrypt_points::<PallasConfig>(&eph_pks, &cts, &sk).unwrap()
            });

            println!(
                "{:>7}  {:>10.1}us  {:>10.1}us  {:>7.2}x",
                n,
                per_t * 1e6,
                bat_t * 1e6,
                per_t / bat_t
            );
        }

        let base = PallasA::rand(&mut rng).into_group();
        let solved = base * Fr::from(123_456u64);
        let garbage = Projective::rand(&mut rng);
        assert!(solve_discrete_log_precomputed::<Projective>(MAX_BALANCE, base, solved).is_some());
        assert!(solve_discrete_log_precomputed::<Projective>(MAX_BALANCE, base, garbage).is_none());
        println!(
            "\n=== discrete log per value, Pallas, {} baby steps ({}) ===",
            MAX_NUM_BABY_STEPS,
            if cfg!(feature = "large_baby_steps") {
                "large_baby_steps on, the deployed setting"
            } else {
                "large_baby_steps off"
            }
        );
        println!(
            "{:>34}  {:>12.1}us",
            "solved, max = MAX_BALANCE",
            time(200, || solve_discrete_log_precomputed::<Projective>(
                MAX_BALANCE,
                base,
                solved
            )) * 1e6
        );
        println!(
            "{:>34}  {:>12.1}us",
            "failed, max = MAX_ASSET_ID",
            time(20, || solve_discrete_log_precomputed::<Projective>(
                MAX_ASSET_ID as u64,
                base,
                garbage
            )) * 1e6
        );
        println!(
            "{:>34}  {:>12.1}us",
            "failed, max = MAX_BALANCE",
            time(3, || solve_discrete_log_precomputed::<Projective>(
                MAX_BALANCE,
                base,
                garbage
            )) * 1e6
        );

        // Full leg scan against per-leg decryption, over participation fractions. `p` is the share of
        // legs the scanning party is sender or receiver of.
        println!(
            "\n=== leg scan: batch_decrypt_legs vs per-leg, hidden asset-id, Pallas ===\n{:>7}  {:>5}  {:>12}  {:>12}  {:>8}",
            "n", "p", "per-leg", "two-round", "speedup"
        );
        for &n in &[64usize, 256, 1024] {
            for &p in &[0.1f64, 0.5, 1.0] {
                let participant = ((n as f64) * p).round() as usize;
                let s = build_legs(n, participant, false, SMALL_AMOUNT_BITS, &mut rng);

                assert_eq!(scan_legs_role_and_amount_together(&s), participant);
                assert_eq!(scan_legs_role_and_amount_separately(&s), participant);

                let reps = (20_000 / n).max(3);
                let per_t = time(reps, || scan_legs_role_and_amount_separately(&s));
                let bat_t = time(reps, || scan_legs_role_and_amount_together(&s));

                println!(
                    "{:>7}  {:>5.1}  {:>10.1}us  {:>10.1}us  {:>7.2}x",
                    n,
                    p,
                    per_t * 1e6,
                    bat_t * 1e6,
                    per_t / bat_t
                );
            }
        }

        println!(
            "\n=== ladder columns: two-round vs fused speculative, hidden asset-id ===\n{:>7}  {:>5}  {:>8}  {:>12}  {:>8}  {:>12}  {:>8}",
            "n", "p", "cols", "two-round", "cols", "speculative", "ratio"
        );
        for &n in &[256usize, 1024] {
            for &p in &[0.1f64, 0.5, 1.0] {
                let participant = ((n as f64) * p).round() as usize;
                let s = build_legs(n, participant, false, SMALL_AMOUNT_BITS, &mut rng);
                let ((role_eph, role_cts), (amount_eph, amount_cts)) =
                    eph_pks_and_cts_role_and_amounts(&s);
                let (spec_eph, spec_cts) = speculative_columns(&s);

                let reps = (20_000 / n).max(3);
                let two_t = time(reps, || {
                    batch_decrypt_points::<PallasConfig>(&role_eph, &role_cts, &s.sk).unwrap();
                    batch_decrypt_points::<PallasConfig>(&amount_eph, &amount_cts, &s.sk).unwrap()
                });
                let spec_t = time(reps, || {
                    batch_decrypt_points::<PallasConfig>(&spec_eph, &spec_cts, &s.sk).unwrap()
                });

                println!(
                    "{:>7}  {:>5.1}  {:>8}  {:>10.1}us  {:>8}  {:>10.1}us  {:>7.2}x",
                    n,
                    p,
                    role_eph.len() + amount_eph.len(),
                    two_t * 1e6,
                    spec_eph.len(),
                    spec_t * 1e6,
                    spec_t / two_t
                );
            }
        }
        println!();
    }

    let mut group = c.benchmark_group("batch_decrypt_points");
    for &n in &[128usize, 1024] {
        let (eph_pks, cts, sk, _enc_gen, _amounts) = build_ciphertexts(n, &mut rng);
        group.bench_function(format!("per_item/{n}"), |b| {
            b.iter(|| black_box(per_item_points(&eph_pks, &cts, &sk)))
        });
        group.bench_function(format!("batch/{n}"), |b| {
            b.iter(|| black_box(batch_decrypt_points::<PallasConfig>(&eph_pks, &cts, &sk).unwrap()))
        });
    }
    group.finish();

    let mut group = c.benchmark_group("leg_scan");
    for &(n, p) in &[(256usize, 0.1f64), (256, 1.0)] {
        let participant = ((n as f64) * p).round() as usize;
        let s = build_legs(n, participant, false, SMALL_AMOUNT_BITS, &mut rng);
        group.bench_function(format!("per_leg/{n}/p{p}"), |b| {
            b.iter(|| black_box(scan_legs_role_and_amount_separately(&s)))
        });
        group.bench_function(format!("two_round/{n}/p{p}"), |b| {
            b.iter(|| black_box(scan_legs_role_and_amount_together(&s)))
        });
    }
    group.finish();
}

/// Same scan with amounts large enough but asset-id still small.
fn bench_leg_scan_large_amounts(c: &mut Criterion) {
    let mut rng = rand::thread_rng();
    let n = LARGE_AMOUNT_LEGS;

    if selected("leg_scan_large_amounts") {
        println!(
            "\n=== leg scan, large amounts: batch_decrypt_legs vs per-leg, n = {n}, p = 1.0, hidden asset-id ===\n{:>7}  {:>12}  {:>12}  {:>8}",
            "bits", "per-leg", "two-round", "speedup"
        );
        for &bits in &LARGE_AMOUNT_BITS {
            let s = build_legs(n, n, false, bits, &mut rng);
            assert_eq!(scan_legs_role_and_amount_together(&s), n);
            assert_eq!(scan_legs_role_and_amount_separately(&s), n);

            let reps = 3;
            let per_t = time(reps, || scan_legs_role_and_amount_separately(&s));
            let bat_t = time(reps, || scan_legs_role_and_amount_together(&s));

            println!(
                "{:>7}  {:>10.1}us  {:>10.1}us  {:>7.2}x",
                bits,
                per_t * 1e6,
                bat_t * 1e6,
                per_t / bat_t
            );
        }
        println!();
    }

    let mut group = c.benchmark_group("leg_scan_large_amounts");
    group.sample_size(10);
    for &bits in &LARGE_AMOUNT_BITS {
        let s = build_legs(n, n, false, bits, &mut rng);
        group.bench_function(format!("two_round/{n}/bits{bits}"), |b| {
            b.iter(|| black_box(scan_legs_role_and_amount_together(&s)))
        });
    }
    group.finish();
}

criterion_group!(
    batch_decrypt_benches,
    bench_batch_decrypt,
    bench_leg_scan_large_amounts
);
criterion_main!(batch_decrypt_benches);
