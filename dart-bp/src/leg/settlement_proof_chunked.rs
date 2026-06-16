//! PoC: chunked settlement proof.
//!
//! Experimental, side-by-side with the existing [`SettlementCreationProof`].

//! Instead of one [`SettlementCreationProof`] (one `BPProof`) over all `N` legs, build several
//! independent proofs over fewer legs and batch-verify them. Because every chunk reuses the same
//! per-chunk-sized generators, batch verification collapses their generator MSMs into one small MSM.
//! Legs are bound together due to same nonce

use crate::Error;
use crate::error::Result;
use crate::leg::settlement_proof::SettlementCreationProof;
use crate::leg::{AssetCommitmentParams, AssetData, Leg, LegEncryption, LegEncryptionRandomness};
use crate::util::batch_verify_bp;
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::Affine;
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::string::ToString;
use ark_std::vec;
use ark_std::vec::Vec;
use bulletproofs::r1cs::VerificationTuple;
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::curve_tree::Root;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use rand_core::CryptoRngCore;

/// A settlement expressed as an ordered set of independent chunks, each its own `BPProof`,
/// with one chunk per curve-tree multipath.
#[derive(Clone, Debug)]
pub struct SettlementCreationProofBatch<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// One [`SettlementCreationProof`] per chunk, in leg order.
    pub chunks: Vec<SettlementCreationProof<L, M, F0, F1, G0, G1>>,
    /// Total number of legs across all chunks (for validation / reporting).
    pub num_legs: u32,
}

impl<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SettlementCreationProofBatch<L, M, F0, F1, G0, G1>
{
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs: Vec<Leg<Affine<G0>>>,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        leg_enc_rands: Vec<LegEncryptionRandomness<F0>>,
        leaf_paths: Vec<CurveTreeWitnessMultiPath<L, M, G1, G0>>,
        asset_data: Vec<AssetData<F0, F1, G0, G1>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let num_legs = legs.len();
        if num_legs == 0 {
            return Err(Error::ProofGenerationError(
                "At least one leg is required to create a settlement proof".to_string(),
            ));
        }
        if num_legs != leg_encs.len() || num_legs != leg_enc_rands.len() {
            return Err(Error::ProofGenerationError(
                "Mismatched number of legs, encryptions, and randomness".to_string(),
            ));
        }

        // Validate the global hidden-leg / asset_data / leaf accounting (mirrors `new`).
        let total_hidden = leg_encs
            .iter()
            .filter(|enc| !enc.is_asset_id_revealed())
            .count();
        if asset_data.len() != total_hidden {
            return Err(Error::ProofGenerationError(
                "asset_data length does not match number of hidden asset-id legs".to_string(),
            ));
        }
        let total_leaves: u32 = leaf_paths.iter().map(|p| p.num_indices()).sum();
        if total_leaves != total_hidden as u32 {
            return Err(Error::ProofGenerationError(
                "Total number of leaves in leaf_paths does not match number of hidden asset-id legs"
                    .to_string(),
            ));
        }

        // (#legs, #hidden) per chunk. trailing revealed legs (if any) form a final multipath-less chunk
        let leaf_counts_per_path = leaf_paths
            .iter()
            .map(|p| p.num_indices() as usize)
            .collect::<Vec<_>>();
        let mut chunk_specs = Vec::new();
        {
            let mut cur_legs = 0;
            let mut cur_hidden = 0;
            let mut mp = 0;
            for enc in &leg_encs {
                cur_legs += 1;
                if !enc.is_asset_id_revealed() {
                    cur_hidden += 1;
                }
                if mp < leaf_counts_per_path.len() && cur_hidden == leaf_counts_per_path[mp] {
                    chunk_specs.push((cur_legs, cur_hidden));
                    cur_legs = 0;
                    cur_hidden = 0;
                    mp += 1;
                }
            }
            if cur_legs > 0 {
                chunk_specs.push((cur_legs, cur_hidden));
            }
        }

        // Build each chunk by consuming the flat inputs in order.
        let mut legs_it = legs.into_iter();
        let mut encs_it = leg_encs.into_iter();
        let mut rands_it = leg_enc_rands.into_iter();
        let mut asset_it = asset_data.into_iter();
        let mut paths_it = leaf_paths.into_iter();

        let mut chunks = Vec::with_capacity(chunk_specs.len());
        for (n_legs, n_hidden) in chunk_specs {
            let chunk_legs: Vec<_> = (&mut legs_it).take(n_legs).collect();
            let chunk_encs: Vec<_> = (&mut encs_it).take(n_legs).collect();
            let chunk_rands: Vec<_> = (&mut rands_it).take(n_legs).collect();
            let chunk_asset: Vec<_> = (&mut asset_it).take(n_hidden).collect();
            // A chunk owns a multipath iff it carries hidden legs.
            let chunk_paths: Vec<_> = if n_hidden > 0 {
                vec![paths_it.next().expect("one multipath per hidden-leg chunk")]
            } else {
                Vec::new()
            };

            let proof = SettlementCreationProof::new::<R, Parameters0, Parameters1>(
                rng,
                chunk_legs,
                chunk_encs,
                chunk_rands,
                chunk_paths,
                chunk_asset,
                asset_tree_root,
                nonce,
                tree_parameters,
                asset_comm_params,
                enc_key_gen,
                enc_gen,
            )?;
            chunks.push(proof);
        }

        Ok(Self {
            chunks,
            num_legs: num_legs as u32,
        })
    }

    pub fn num_chunks(&self) -> usize {
        self.chunks.len()
    }

    pub fn total_proof_size(&self) -> usize {
        self.chunks.iter().map(|c| c.compressed_size()).sum()
    }

    /// Run the per-chunk sigma-protocol verification and return BP verification tuples
    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        rng: &mut R,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(
        Vec<VerificationTuple<Affine<G1>>>,
        Vec<VerificationTuple<Affine<G0>>>,
    )> {
        let expected: usize = self.chunks.iter().map(|c| c.leg_proofs.len()).sum();
        if leg_encs.len() != expected {
            return Err(Error::ProofVerificationError(
                "Number of leg encryptions does not match total legs across chunks".to_string(),
            ));
        }

        let mut encs_it = leg_encs.into_iter();
        let mut even_tuples = Vec::with_capacity(self.chunks.len());
        let mut odd_tuples = Vec::with_capacity(self.chunks.len());
        for chunk in &self.chunks {
            let chunk_encs: Vec<_> = (&mut encs_it).take(chunk.leg_proofs.len()).collect();
            let (even, odd) = chunk.verify_and_return_tuples::<R, Parameters0, Parameters1>(
                chunk_encs,
                asset_tree_root,
                Vec::new(), // enc_keys: empty (hidden-asset legs only)
                Vec::new(), // med_keys: empty
                Vec::new(), // public_enc_keys: empty
                nonce,
                tree_parameters,
                asset_comm_params,
                enc_key_gen,
                enc_gen,
                rng,
                rmc.as_deref_mut(),
            )?;
            even_tuples.push(even);
            odd_tuples.push(odd);
        }
        Ok((even_tuples, odd_tuples))
    }

    pub fn verify_batched_bp<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        rng: &mut R,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<()> {
        let (even_tuples, odd_tuples) = self
            .verify_and_return_tuples::<R, Parameters0, Parameters1>(
                rng,
                leg_encs,
                asset_tree_root,
                nonce,
                tree_parameters,
                asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )?;
        batch_verify_bp(
            even_tuples,
            odd_tuples,
            tree_parameters.even_parameters.pc_gens(),
            tree_parameters.odd_parameters.pc_gens(),
            tree_parameters.even_parameters.bp_gens(),
            tree_parameters.odd_parameters.bp_gens(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::SettlementCreationProofBatch;
    use crate::keys::keygen_enc;
    use crate::leg::settlement_proof::SettlementCreationProof;
    use crate::leg::{AssetCommitmentParams, AssetData, Leg, LegEncConfig};
    use crate::util::{add_verification_tuples_batches_to_rmc, batch_verify_bp, verify_rmc};
    use ark_ec::CurveGroup;
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use ark_pallas::{Fr as PallasScalar, PallasConfig};
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use ark_vesta::{Fr as VestaScalar, VestaConfig};
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use curve_tree_relations::curve_tree::CurveTree;
    use curve_tree_relations::parameters::SelRerandProofParametersNew;
    use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
    use std::time::Instant;

    type PallasParameters = PallasConfig;
    type VestaParameters = VestaConfig;

    /// One row of the sweep result table. Times in milliseconds.
    struct Row {
        label: String,
        num_chunks: usize,
        prover_ms: f64,
        collect_tuples_ms: f64,
        batched_msm_ms: f64,
        /// collect_tuples + batched MSM (the `batch_verify_bp` path).
        verifier_batched_ms: f64,
        /// Full RandomizedMultChecker path: sigma + BP folded into one accumulator, one
        /// combined MSM per curve.
        verifier_rmc_ms: f64,
        proof_bytes: usize,
    }

    fn ms(d: std::time::Duration) -> f64 {
        d.as_secs_f64() * 1000.0
    }

    #[test]
    fn settlement_chunk() {
        // Mirrors `large_settlement_verification`'s shape (one hidden-asset settlement, all
        // legs reference asset_id=1). Keeping `N=20` matches the existing baseline so
        // cross-comparison is direct.
        const NUM_GENS: usize = 1 << 17;
        const L: usize = 64;
        const M: usize = 8; // type-level multipath cap

        let height = 4;
        let num_legs: usize = 20;
        let nonce = b"settlement_chunk_sweep_nonce";
        let amount: u64 = 100;

        // Effective chunk sizes to measure = leaves per multipath (1..=M). g = chunk size K.
        let g_values: Vec<usize> = vec![1, 2, 4, M];

        let mut rng = rand::thread_rng();
        let label = b"settlement_chunk_sweep_label";

        let asset_tree_params = SelRerandProofParametersNew::<
            VestaParameters,
            PallasParameters,
            _,
            _,
        >::new_using_label(label, NUM_GENS as u32, NUM_GENS as u32)
        .unwrap();

        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 1;
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors,
            0,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
        let enc_keys = vec![pk_a_e.0];
        let med_keys = vec![];

        let asset_id = 1u32;
        let asset_data = AssetData::<_, _, PallasParameters, VestaParameters>::new(
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.sl_params.delta,
        )
        .unwrap();
        let commitments = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(height),
        );
        let root = asset_tree.root_node();

        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        // Build the legs once; every row reuses them. The only thing that changes per row is
        // how the leaves are grouped into multipaths (= chunk size).
        let mut legs = Vec::with_capacity(num_legs);
        let mut leg_encs = Vec::with_capacity(num_legs);
        let mut leg_enc_rands = Vec::with_capacity(num_legs);
        let mut asset_data_vec = Vec::with_capacity(num_legs);

        for _ in 0..num_legs {
            let leg = Leg::new(
                pk_s_e.0,
                pk_r_e.0,
                amount,
                asset_id,
                vec![pk_a_e.0],
                vec![],
                vec![],
            )
            .unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt(
                    &mut rng,
                    LegEncConfig {
                        reveal_asset_id: false,
                        parties_see_each_other: true,
                    },
                    enc_key_gen,
                    enc_gen,
                )
                .unwrap();
            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
            asset_data_vec.push(asset_data.clone());
        }

        // Build `ceil(num_legs / g)` multipaths, each batching `g` leaves (all referencing
        // leaf 0, like `large_settlement_verification`). With one chunk per multipath, this
        // sets the chunk size to `g`.
        let build_paths = |g: usize| {
            let indices = vec![0u32; num_legs];
            let mut paths = Vec::new();
            for chunk in indices.chunks(g) {
                paths.push(asset_tree.get_paths_to_leaves(chunk).unwrap());
            }
            paths
        };

        println!(
            "\n=== Settlement chunk-sweep: N={} legs, L={}, M={}, height={}, all hidden-asset ===",
            num_legs, L, M, height
        );
        println!("(chunk = one multipath; g = leaves per multipath = effective chunk size K)");

        let mut rows: Vec<Row> = Vec::new();

        // ---- Monolith baseline (today's SettlementCreationProof::new + verify), g=M ----
        {
            let paths = build_paths(M);

            let t0 = Instant::now();
            let proof =
                SettlementCreationProof::<L, M, _, _, _, _>::new::<_, PallasParams, VestaParams>(
                    &mut rng,
                    legs.clone(),
                    leg_encs.clone(),
                    leg_enc_rands.clone(),
                    paths,
                    asset_data_vec.clone(),
                    &root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                )
                .unwrap();
            let prover_time = t0.elapsed();
            let proof_bytes = proof.compressed_size();

            let t0 = Instant::now();
            let (even_tuple, odd_tuple) = proof
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    leg_encs.clone(),
                    &root,
                    vec![],
                    vec![],
                    vec![],
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
            let collect_t = t0.elapsed();

            let t0 = Instant::now();
            batch_verify_bp(
                vec![even_tuple],
                vec![odd_tuple],
                asset_tree_params.even_parameters.pc_gens(),
                asset_tree_params.odd_parameters.pc_gens(),
                asset_tree_params.even_parameters.bp_gens(),
                asset_tree_params.odd_parameters.bp_gens(),
            )
            .unwrap();
            let batch_t = t0.elapsed();

            // RandomizedMultChecker path: fold sigma + BP into one accumulator per curve
            let t0 = Instant::now();
            let mut rmc_even = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
            let mut rmc_odd = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    leg_encs.clone(),
                    &root,
                    vec![],
                    vec![],
                    vec![],
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    Some((&mut rmc_even, &mut rmc_odd)),
                )
                .unwrap();
            verify_rmc(rmc_even, rmc_odd).unwrap();
            let rmc_t = t0.elapsed();

            rows.push(Row {
                label: "monolith (baseline)".to_string(),
                num_chunks: 1,
                prover_ms: ms(prover_time),
                collect_tuples_ms: ms(collect_t),
                batched_msm_ms: ms(batch_t),
                verifier_batched_ms: ms(collect_t) + ms(batch_t),
                verifier_rmc_ms: ms(rmc_t),
                proof_bytes,
            });
        }

        // ---- Chunked: one chunk per multipath, swept over g (= chunk size) ----
        for &g in &g_values {
            let paths = build_paths(g);

            let t0 = Instant::now();
            let batch = SettlementCreationProofBatch::<L, M, _, _, _, _>::new::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                legs.clone(),
                leg_encs.clone(),
                leg_enc_rands.clone(),
                paths,
                asset_data_vec.clone(),
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
            let prover_time = t0.elapsed();
            let proof_bytes = batch.total_proof_size();
            let num_chunks = batch.num_chunks();

            let t0 = Instant::now();
            let (even_tuples, odd_tuples) = batch
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    &mut rng,
                    leg_encs.clone(),
                    &root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
            let collect_t = t0.elapsed();

            let t0 = Instant::now();
            batch_verify_bp(
                even_tuples,
                odd_tuples,
                asset_tree_params.even_parameters.pc_gens(),
                asset_tree_params.odd_parameters.pc_gens(),
                asset_tree_params.even_parameters.bp_gens(),
                asset_tree_params.odd_parameters.bp_gens(),
            )
            .unwrap();
            let batch_t = t0.elapsed();

            // RandomizedMultChecker path over all chunks: fold sigma + every chunk's BP tuple
            // into one accumulator per curve
            let t0 = Instant::now();
            let mut rmc_even = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
            let mut rmc_odd = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));
            let (even_tuples, odd_tuples) = batch
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    &mut rng,
                    leg_encs.clone(),
                    &root,
                    nonce,
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    Some(&mut rmc_odd),
                )
                .unwrap();
            add_verification_tuples_batches_to_rmc(
                even_tuples,
                odd_tuples,
                asset_tree_params.even_parameters.pc_gens(),
                asset_tree_params.odd_parameters.pc_gens(),
                asset_tree_params.even_parameters.bp_gens(),
                asset_tree_params.odd_parameters.bp_gens(),
                &mut rmc_even,
                &mut rmc_odd,
            )
            .unwrap();
            verify_rmc(rmc_even, rmc_odd).unwrap();
            let rmc_t = t0.elapsed();

            rows.push(Row {
                label: format!("chunked g={} (K={})", g, g),
                num_chunks,
                prover_ms: ms(prover_time),
                collect_tuples_ms: ms(collect_t),
                batched_msm_ms: ms(batch_t),
                verifier_batched_ms: ms(collect_t) + ms(batch_t),
                verifier_rmc_ms: ms(rmc_t),
                proof_bytes,
            });
        }

        println!(
            "\n{:<22} {:>7} {:>11} {:>14} {:>13} {:>15} {:>13} {:>11}",
            "config",
            "chunks",
            "prover(ms)",
            "collect(ms)",
            "batchMSM(ms)",
            "verif batch(ms)",
            "verif RMC(ms)",
            "proof(B)",
        );
        println!("{}", "-".repeat(112));
        for row in &rows {
            println!(
                "{:<22} {:>7} {:>11.1} {:>14.1} {:>13.1} {:>15.1} {:>13.1} {:>11}",
                row.label,
                row.num_chunks,
                row.prover_ms,
                row.collect_tuples_ms,
                row.batched_msm_ms,
                row.verifier_batched_ms,
                row.verifier_rmc_ms,
                row.proof_bytes,
            );
        }
    }
}
