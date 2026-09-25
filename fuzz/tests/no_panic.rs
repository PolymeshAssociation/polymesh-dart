//! Property tests: no verifier entry point may panic on decodable input.
//!
//! Three input families, all funnelled through `decode_and_verify` / `exercise_leg_encrypted`:
//!  1. every valid seed request (must verify `Ok`);
//!  2. mutated-valid requests (random byte-level mutations of a seed);
//!  3. purely random bytes.
//!
//! Run with `cargo test -p polymesh-dart-fuzz --release`. `PROPTEST_CASES` scales the case count.

use codec::Encode;
use polymesh_dart_fuzz::mutate::{ALL_MUTATIONS, apply, mutate_n};
use polymesh_dart_fuzz::{VerifyDartAssetRequest, decode_and_verify, seeds};
use proptest::prelude::*;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

fn cases(default: u32) -> u32 {
    std::env::var("PROPTEST_CASES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

#[test]
fn all_seed_requests_verify() {
    for s in seeds() {
        let bytes = s.encoded();
        // Round-trip through SCALE like the pallet -> worker boundary does.
        let res = decode_and_verify(&bytes).expect("seed must decode");
        assert!(res.is_ok(), "seed `{}` failed to verify: {res:?}", s.name);
        let decoded = codec::Decode::decode(&mut &bytes[..])
            .map(|r: VerifyDartAssetRequest| r.encode())
            .unwrap();
        assert_eq!(
            decoded, bytes,
            "seed `{}` is not SCALE round-trip stable",
            s.name
        );
    }
    assert!(seeds().len() >= 20, "expected one seed per request variant");
}

/// Single-step mutations of every seed at sampled byte offsets (every `stride`-th byte; set
/// `DART_FUZZ_EXHAUSTIVE=1` to sweep every offset, ~15 min in release). Truncation is always
/// exhaustive over lengths since it is cheap (fails at SCALE decode).
#[test]
fn exhaustive_single_byte_mutations_do_not_panic() {
    let stride = if std::env::var_os("DART_FUZZ_EXHAUSTIVE").is_some() {
        1
    } else {
        29
    };
    for (k, s) in seeds().iter().enumerate() {
        let bytes = s.encoded();
        // Truncate at every length.
        for len in 0..bytes.len() {
            let _ = decode_and_verify(&bytes[..len]);
        }
        // Zero / 0xff / flip-msb / flip-lsb sampled bytes (offset phase differs per seed).
        for i in (k % stride..bytes.len()).step_by(stride) {
            for v in [0x00u8, 0xff, bytes[i] ^ 0x80, bytes[i] ^ 0x01] {
                let mut m = bytes.clone();
                m[i] = v;
                let _ = decode_and_verify(&m);
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: cases(64),
        max_shrink_iters: 0,
        .. ProptestConfig::default()
    })]

    /// Mutated-valid proofs: a few random mutations applied to a random seed.
    #[test]
    fn mutated_seed_requests_do_not_panic(
        seed_idx in any::<usize>(),
        rng_seed in any::<u64>(),
        n_mut in 1usize..6,
    ) {
        let seeds = seeds();
        let s = &seeds[seed_idx % seeds.len()];
        let mut bytes = s.encoded();
        let mut rng = ChaCha20Rng::seed_from_u64(rng_seed);
        mutate_n(&mut bytes, n_mut, &mut rng);
        let _ = decode_and_verify(&bytes);
    }

    /// One specific mutation kind at a time (so a regression pins the kind).
    #[test]
    fn each_mutation_kind_does_not_panic(
        seed_idx in any::<usize>(),
        rng_seed in any::<u64>(),
        m_idx in 0usize..ALL_MUTATIONS.len(),
    ) {
        let seeds = seeds();
        let s = &seeds[seed_idx % seeds.len()];
        let mut bytes = s.encoded();
        let mut rng = ChaCha20Rng::seed_from_u64(rng_seed);
        apply(ALL_MUTATIONS[m_idx], &mut bytes, &mut rng);
        let _ = decode_and_verify(&bytes);
    }

    /// Random bytes (mostly rejected at decode; exercises the SCALE layer and short inputs).
    #[test]
    fn random_bytes_do_not_panic(bytes in proptest::collection::vec(any::<u8>(), 0..4096)) {
        let _ = decode_and_verify(&bytes);
    }

    /// Random bytes prefixed with a valid variant tag (reaches the per-variant decoders).
    #[test]
    fn random_tagged_bytes_do_not_panic(
        tag in 0u8..20,
        bytes in proptest::collection::vec(any::<u8>(), 0..2048),
    ) {
        let mut data = vec![tag];
        data.extend(bytes);
        let _ = decode_and_verify(&data);
    }
}
