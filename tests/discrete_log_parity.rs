//! Correctness gate for replacing the repo's BSGS discrete-log solver
//! (`polymesh_dart_bp::discrete_log::solve_discrete_log_bsgs`) with the precomputed-table
//! solver in `dock_crypto_utils::solve_discrete_log`. Asserts old, new (cache), new
//! (`with_table_size`), and new (`given_table`) all agree with ground truth on Pallas across
//! table boundaries, the `u32`/chunk boundary, both production search spaces (amount = `MAX_BALANCE`,
//! asset-id = `MAX_ASSET_ID`), `min > 0`, and out-of-range inputs.

use ark_pallas::{Fr, Projective};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;

use dock_crypto_utils::solve_discrete_log::{
    BabyStepsTable, solve_discrete_log_bsgs_precomputed,
    solve_discrete_log_bsgs_precomputed_with_table_size, solve_discrete_log_given_table,
};
use polymesh_dart_bp::discrete_log::solve_discrete_log_bsgs;
use polymesh_dart_common::{MAX_ASSET_ID, MAX_BALANCE};

const T16: u64 = 1 << 16;
const T21: u64 = 1 << 21;

fn base() -> Projective {
    hash_to_pallas(b"parity", b"enc-gen")
}

fn target(base: Projective, dl: u64) -> Projective {
    base * Fr::from(dl)
}

// New solver over a freshly built (uncached) table, mirroring the sizing `_with_table_size` uses.
fn solve_new_given_table(
    max: u64,
    min: u64,
    table_size: u64,
    base: Projective,
    t: Projective,
) -> Option<u64> {
    let width = max - min;
    let m = table_size.min(width).max(1);
    let table = BabyStepsTable::<Projective>::new(base, m);
    solve_discrete_log_given_table(&table, base, min, width, t)
}

// Assert every `min == 0` contender agrees with `Some(dl)` for `base * dl` under bound `max`.
fn assert_all_agree(max: u64, dl: u64) {
    let base = base();
    let t = target(base, dl);
    assert_eq!(
        solve_discrete_log_bsgs(max, base, t),
        Some(dl),
        "old, max={max}, dl={dl}"
    );
    assert_eq!(
        solve_discrete_log_bsgs_precomputed(max, 0, base, t),
        Some(dl),
        "new cache(default), max={max}, dl={dl}"
    );
    for m in [T16, T21] {
        assert_eq!(
            solve_discrete_log_bsgs_precomputed_with_table_size(max, 0, m, base, t),
            Some(dl),
            "new cache(m={m}), max={max}, dl={dl}"
        );
        assert_eq!(
            solve_new_given_table(max, 0, m, base, t),
            Some(dl),
            "new given_table(m={m}), max={max}, dl={dl}"
        );
    }
}

#[test]
fn parity_amount_space_boundaries() {
    // Table boundaries and small/medium amounts, bounded so the giant walk stays cheap.
    for dl in [
        0u64, 1, 2, 10, 100, 1_000, 10_000, 65_535, 65_536, 65_537, 100_000, 131_071, 131_072,
        262_143, 262_144, 262_145, 1_000_000, 2_097_151, 2_097_152, 2_097_153, 5_000_000,
    ] {
        assert_all_agree(MAX_BALANCE, dl);
    }
}

#[test]
fn parity_asset_id_space() {
    let max = MAX_ASSET_ID as u64;
    for dl in [0u64, 1, 2, 65_536, 1_000_000, 1u64 << 24, max - 1, max] {
        assert_all_agree(max, dl);
    }
}

// The `u32`/`2^32` chunk boundary: a small table forces the new solver's center range to span more
// than one `2^32`-wide chunk, and the old solver crosses its parallel `u32::MAX` chunk boundary.
#[test]
fn parity_chunk_boundary() {
    let base = base();
    let max = 1u64 << 33;
    for dl in [(1u64 << 32) - 1, 1u64 << 32, (1u64 << 32) + 6789] {
        let t = target(base, dl);
        assert_eq!(
            solve_discrete_log_bsgs(max, base, t),
            Some(dl),
            "old, dl={dl}"
        );
        assert_eq!(
            solve_discrete_log_bsgs_precomputed(max, 0, base, t),
            Some(dl),
            "new cache(default), dl={dl}"
        );
        assert_eq!(
            solve_new_given_table(max, 0, T16, base, t),
            Some(dl),
            "new given_table(m=2^16), dl={dl}"
        );
    }
}

#[test]
fn parity_min_bound() {
    let base = base();
    let (min, max) = (1_000u64, 5_000u64);
    for dl in [min, 3_000, max] {
        let t = target(base, dl);
        assert_eq!(
            solve_discrete_log_bsgs_precomputed(max, min, base, t),
            Some(dl),
            "dl={dl}"
        );
        assert_eq!(
            solve_new_given_table(max, min, T16, base, t),
            Some(dl),
            "given, dl={dl}"
        );
    }
    // Below `min` and above `max` are not returned.
    assert_eq!(
        solve_discrete_log_bsgs_precomputed(max, min, base, target(base, min - 1)),
        None
    );
    assert_eq!(
        solve_discrete_log_bsgs_precomputed(max, min, base, target(base, max + 1)),
        None
    );
}

// The new solver strictly enforces `max`: a target whose DL exceeds `max` is rejected even when it
// would sit inside the baby-steps table.
#[test]
fn new_solver_enforces_max() {
    let base = base();
    let t = target(base, 10);
    assert_eq!(solve_discrete_log_bsgs_precomputed(8, 0, base, t), None);
    assert_eq!(solve_new_given_table(8, 0, T16, base, t), None);
}
