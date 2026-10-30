use ark_ec::CurveGroup;
use ark_std::vec::Vec;
use dock_crypto_utils::solve_discrete_log::{
    solve_discrete_log_bsgs_precomputed_batch, solve_discrete_log_bsgs_precomputed_with_table_size,
};

#[cfg(feature = "large_baby_steps")]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 21;
#[cfg(not(feature = "large_baby_steps"))]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 17;

/// Discrete log in `[0, max]` via a precomputed table of `MAX_NUM_BABY_STEPS` baby steps.
pub fn solve_discrete_log_precomputed<G: CurveGroup + Send + Sync + 'static>(
    max: u64,
    base: G,
    target: G,
) -> Option<u64> {
    solve_discrete_log_bsgs_precomputed_with_table_size(max, 0, MAX_NUM_BABY_STEPS, base, target)
}

/// Discrete log in `[0, max]` for many targets sharing one `base`, one entry per target in order.
pub fn solve_discrete_log_precomputed_batch<G: CurveGroup + Send + Sync + 'static>(
    max: u64,
    base: G,
    targets: &[G],
) -> Vec<Option<u64>> {
    solve_discrete_log_bsgs_precomputed_batch(max, 0, base, targets)
}

#[cfg(all(test, feature = "host_proofs"))]
mod tests {
    use super::*;
    use ark_pallas::Projective;
    use ark_std::{UniformRand, vec::Vec};
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    #[test]
    fn precomputed_single_and_batch() {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let base = Projective::rand(&mut rng);
        let max = 1u64 << 20;
        let values: Vec<u64> = [0, 1, 5, 1 << 17, (1 << 17) + 3, max - 1, max].to_vec();
        let targets: Vec<Projective> = values
            .iter()
            .map(|v| base * ark_pallas::Fr::from(*v))
            .collect();
        for (v, t) in values.iter().zip(targets.iter()) {
            assert_eq!(solve_discrete_log_precomputed(max, base, *t), Some(*v));
        }
        let solved = solve_discrete_log_precomputed_batch(max, base, &targets);
        assert_eq!(solved, values.iter().map(|v| Some(*v)).collect::<Vec<_>>());
        assert!(solve_discrete_log_precomputed_batch(max, base, &[]).is_empty());
        let out_of_range = base * ark_pallas::Fr::from(max + 1);
        assert_eq!(
            solve_discrete_log_precomputed(max, base, out_of_range),
            None
        );
    }
}
