//! Property tests for the on-chain `LegEncrypted` encoding and the v0 -> v1 migration path.

use codec::Encode;
use polymesh_dart::LegEncrypted;
use polymesh_dart_fuzz::mutate::mutate_n;
use polymesh_dart_fuzz::{exercise_leg_encrypted, leg_encryptions};
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
fn from_v0_on_valid_v1_legs_is_err_or_identity() {
    // The chain migration runs `from_v0()` over every stored leg and keeps the result on `Ok`.
    // For a leg that is already v1 this must either fail cleanly or be a no-op:
    //  * hidden asset-id: `mediators` is `Some(vec)` (`0x01` + compact len) which the v0 decoder
    //    reads as a compact vec length and then runs out of bytes -> `Err`;
    //  * revealed asset-id: `mediators` is `None` (`0x00`) which is byte-identical to the v0
    //    empty mediator vec, so the conversion succeeds and re-encodes to the same bytes.
    for (name, leg) in leg_encryptions() {
        match leg.from_v0() {
            Err(_) => {}
            Ok(converted) => assert_eq!(
                converted.encode(),
                leg.encode(),
                "v1 leg `{name}` converted as v0 to different bytes"
            ),
        }
        // and exercising every accessor on a well-formed leg must not panic
        exercise_leg_encrypted(&leg.encode()).expect("valid leg must decode");
    }
}

#[test]
fn exhaustive_single_byte_leg_mutations_do_not_panic() {
    for (_, leg) in leg_encryptions() {
        let bytes = leg.encode();
        for len in 0..bytes.len() {
            let _ = exercise_leg_encrypted(&bytes[..len]);
        }
        for i in 0..bytes.len() {
            for v in [0x00u8, 0x01, 0xff, bytes[i] ^ 0x80] {
                let mut m = bytes.clone();
                m[i] = v;
                let _ = exercise_leg_encrypted(&m);
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: cases(256),
        max_shrink_iters: 0,
        .. ProptestConfig::default()
    })]

    #[test]
    fn mutated_legs_do_not_panic(
        leg_idx in any::<usize>(),
        rng_seed in any::<u64>(),
        n_mut in 1usize..8,
    ) {
        let legs = leg_encryptions();
        let (_, leg) = &legs[leg_idx % legs.len()];
        let mut bytes = leg.encode();
        let mut rng = ChaCha20Rng::seed_from_u64(rng_seed);
        mutate_n(&mut bytes, n_mut, &mut rng);
        let _ = exercise_leg_encrypted(&bytes);
    }

    #[test]
    fn from_v0_on_random_bytes_never_panics(bytes in proptest::collection::vec(any::<u8>(), 0..1024)) {
        // Arbitrary bytes wrapped as the SCALE `BoundedVec<u8>` payload of a `LegEncrypted`.
        let wrapped = bytes.encode();
        if let Ok(leg) = <LegEncrypted as codec::Decode>::decode(&mut &wrapped[..]) {
            let _ = leg.from_v0();
            let _ = leg.decode();
        }
        polymesh_dart_fuzz::exercise_curve_tree_root(&bytes);
    }
}
