#![no_main]
//! Coverage-guided fuzzing of `LegEncrypted` (the on-chain leg encoding): decode, `from_v0()`,
//! mediator lookup and the client-side decryption helpers must never panic.

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _ = polymesh_dart_fuzz::exercise_leg_encrypted(data);
});
