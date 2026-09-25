//! Diagnostic: how far do mutated seeds get? (decode failure vs verify Err vs verify Ok)
//! `cargo run -p polymesh-dart-fuzz --release --example mutation_stats`
use codec::Decode;
use polymesh_dart_fuzz::mutate::{ALL_MUTATIONS, apply};
use polymesh_dart_fuzz::{VerifyDartAssetRequest, seeds};
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use std::time::Instant;

fn main() {
    let n: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(200);
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    for s in seeds() {
        let bytes = s.encoded();
        let (mut dec_fail, mut ver_err, mut ver_ok) = (0, 0, 0);
        let mut slow = 0u128;
        let t0 = Instant::now();
        for i in 0..n {
            let mut m = bytes.clone();
            apply(ALL_MUTATIONS[i % ALL_MUTATIONS.len()], &mut m, &mut rng);
            match VerifyDartAssetRequest::decode(&mut &m[..]) {
                Err(_) => dec_fail += 1,
                Ok(req) => {
                    let t = Instant::now();
                    match req.verify() {
                        Ok(()) => ver_ok += 1,
                        Err(_) => ver_err += 1,
                    }
                    let dt = t.elapsed().as_micros();
                    if dt > 5_000 {
                        slow += 1;
                    }
                }
            }
        }
        println!(
            "{:<38} len={:>6}  decode_fail={:>4} verify_err={:>4} verify_ok={:>3} deep(>5ms)={:>3}  {:?}",
            s.name,
            bytes.len(),
            dec_fail,
            ver_err,
            ver_ok,
            slow,
            t0.elapsed()
        );
    }
}
