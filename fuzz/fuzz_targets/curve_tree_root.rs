#![no_main]
//! Coverage-guided fuzzing of `CompressedCurveTreeRoot` decompression (`root_node()`).

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    polymesh_dart_fuzz::exercise_curve_tree_root(data);
});
