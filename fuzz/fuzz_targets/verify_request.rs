#![no_main]
//! Coverage-guided fuzzing of the worker verification dispatcher: arbitrary bytes ->
//! `VerifyDartAssetRequest::decode` -> `verify`. Any panic is a finding.
//!
//! Seed the corpus with the valid requests: `cargo run -p polymesh-dart-fuzz --example gen_corpus`
//! then `cargo fuzz run --features libfuzzer verify_request`.

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let _ = polymesh_dart_fuzz::decode_and_verify(data);
});
