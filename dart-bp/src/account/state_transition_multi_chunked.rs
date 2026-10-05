//! PoC: chunked multi-asset state transition proof
//!
//! Experimental, side-by-side with the existing [`MultiAssetStateTransitionProof`]. Same chunking idea as
//! [`crate::leg::settlement_proof_chunked`]. Each chunk's transcripts start with the chunk's index, the
//! number of chunks and a digest of the public inputs of all accounts.

use crate::account::AccountCommitmentKeyTrait;
use crate::account::state_transition::{
    AccountStateTransitionProofBuilder, AccountStateTransitionProofVerifier,
};
use crate::account::state_transition_multi::MultiAssetStateTransitionProof;
use crate::auth_proofs::NULLIFIER_LABEL;
use crate::error::Result;
use crate::util::{
    BPProof, batch_digest, batch_verify_bp, chunk_transcript, get_verification_tuples_with_rng,
    prove_with_rng,
};
use crate::{
    Error, LEG_ACTION_LABEL, LEG_ENC_LABEL, NONCE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL,
    UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::Affine;
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{Prover, VerificationTuple, Verifier};
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::curve_tree::Root;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;

pub const MULTI_ASSET_BATCH_LABEL: &[u8; 17] = b"multi-asset-batch";

/// A multi-asset transition expressed as an ordered set of independent chunks, each its own
/// `BPProof`, with one chunk per curve-tree multipath.
#[derive(Clone, Debug)]
pub struct MultiAssetStateTransitionProofBatch<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub chunks: Vec<MultiAssetStateTransitionProof<L, M, F0, F1, G0, G1>>,
    /// Nullifiers in original (concatenated) account order: chunk 0's nullifiers, then
    /// chunk 1's, etc. (each chunk in the order its builders were supplied).
    pub nullifiers: Vec<Affine<G0>>,
    pub num_accounts: u32,
}

impl<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MultiAssetStateTransitionProofBatch<L, M, F0, F1, G0, G1>
{
    /// Build the chunked MAST proof: one fresh `BPProof` per `leaf_paths` entry (one chunk
    /// per multipath).
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        account_builders: Vec<AccountStateTransitionProofBuilder<L, F0, F1, G0, G1>>,
        leaf_paths: Vec<CurveTreeWitnessMultiPath<L, M, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>> + Clone,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let num_accounts = account_builders.len();
        if num_accounts == 0 {
            return Err(Error::ProofGenerationError(
                "At least one account is required".to_string(),
            ));
        }
        let total_leaves: u32 = leaf_paths.iter().map(|p| p.num_indices()).sum();
        if total_leaves != num_accounts as u32 {
            return Err(Error::ProofGenerationError(
                "Total number of leaves in leaf_paths does not match number of accounts"
                    .to_string(),
            ));
        }

        let accounts_digest = Self::builders_digest(&account_builders, &account_comm_key)?;
        let num_chunks = leaf_paths.len();

        let mut builders_it = account_builders.into_iter();
        let mut chunks = Vec::with_capacity(num_chunks);
        let mut nullifiers_all: Vec<Affine<G0>> = Vec::with_capacity(num_accounts);
        for (chunk_idx, mp) in leaf_paths.into_iter().enumerate() {
            let n = mp.num_indices() as usize;
            let chunk_builders: Vec<_> = (&mut builders_it).take(n).collect();
            let mut even_prover = Prover::new(
                &account_tree_params.even_parameters.pc_gens(),
                chunk_transcript(TXN_EVEN_LABEL, num_chunks, chunk_idx, &accounts_digest)?,
            );
            let mut odd_prover = Prover::new(
                &account_tree_params.odd_parameters.pc_gens(),
                chunk_transcript(TXN_ODD_LABEL, num_chunks, chunk_idx, &accounts_digest)?,
            );
            let (mut proof, mut nullifiers) =
                MultiAssetStateTransitionProof::new_with_given_prover::<R, Parameters0, Parameters1>(
                    rng,
                    chunk_builders,
                    vec![mp],
                    tree_root,
                    account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    &mut even_prover,
                    &mut odd_prover,
                )?;
            let (even_proof, odd_proof) = prove_with_rng(
                even_prover,
                odd_prover,
                &account_tree_params.even_parameters.bp_gens(),
                &account_tree_params.odd_parameters.bp_gens(),
                rng,
            )?;
            proof.r1cs_proof = Some(BPProof {
                even_proof,
                odd_proof,
            });
            nullifiers_all.append(&mut nullifiers);
            chunks.push(proof);
        }

        Ok(Self {
            chunks,
            nullifiers: nullifiers_all,
            num_accounts: num_accounts as u32,
        })
    }

    pub fn num_chunks(&self) -> usize {
        self.chunks.len()
    }

    /// Digest of the nonce, updated commitment, nullifier and legs of all accounts, in account order.
    fn builders_digest(
        builders: &[AccountStateTransitionProofBuilder<L, F0, F1, G0, G1>],
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<[u8; 32]> {
        let mut transcript = MerlinTranscript::new(MULTI_ASSET_BATCH_LABEL);
        for builder in builders {
            let nullifier = builder.host.account.nullifier(account_comm_key);
            add_to_transcript!(
                transcript,
                NONCE_LABEL,
                builder.host.nonce,
                UPDATED_ACCOUNT_COMMITMENT_LABEL,
                builder.host.updated_account_commitment,
                NULLIFIER_LABEL,
                nullifier
            );
            for leg in &builder.host.legs {
                add_to_transcript!(
                    transcript,
                    LEG_ENC_LABEL,
                    leg.encryption,
                    LEG_ENC_LABEL,
                    leg.party_eph_pk,
                    LEG_ACTION_LABEL,
                    leg.action_tag()
                );
            }
        }
        Ok(batch_digest(transcript))
    }

    /// Verifier-side counterpart of [`Self::builders_digest`].
    fn verifiers_digest(
        verifiers: &[AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>],
    ) -> Result<[u8; 32]> {
        let mut transcript = MerlinTranscript::new(MULTI_ASSET_BATCH_LABEL);
        for verifier in verifiers {
            add_to_transcript!(
                transcript,
                NONCE_LABEL,
                verifier.nonce,
                UPDATED_ACCOUNT_COMMITMENT_LABEL,
                verifier.updated_account_commitment,
                NULLIFIER_LABEL,
                verifier.nullifier
            );
            for leg in &verifier.legs {
                add_to_transcript!(
                    transcript,
                    LEG_ENC_LABEL,
                    leg.encryption,
                    LEG_ENC_LABEL,
                    leg.party_eph_pk,
                    LEG_ACTION_LABEL,
                    leg.action_tag()
                );
            }
        }
        Ok(batch_digest(transcript))
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
        account_verifiers: Vec<AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>> + Clone,
        enc_gen: Affine<G0>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(
        Vec<VerificationTuple<Affine<G0>>>,
        Vec<VerificationTuple<Affine<G1>>>,
    )> {
        let expected: usize = self.chunks.iter().map(|c| c.account_proofs.len()).sum();
        if account_verifiers.len() != expected {
            return Err(Error::ProofVerificationError(
                "Number of account verifiers does not match total accounts across chunks"
                    .to_string(),
            ));
        }

        // Each chunk rejects a repeated nullifier among its own accounts. This covers the whole batch.
        let mut seen_nullifiers = Vec::with_capacity(account_verifiers.len());
        for verifier in &account_verifiers {
            if seen_nullifiers.contains(&verifier.nullifier) {
                return Err(Error::ProofVerificationError(
                    "Repeated nullifier in multi-asset state transition proof batch".to_string(),
                ));
            }
            seen_nullifiers.push(verifier.nullifier);
        }

        let accounts_digest = Self::verifiers_digest(&account_verifiers)?;
        let num_chunks = self.chunks.len();

        let mut verifiers_it = account_verifiers.into_iter();
        let mut even_tuples = Vec::with_capacity(num_chunks);
        let mut odd_tuples = Vec::with_capacity(num_chunks);
        for (chunk_idx, chunk) in self.chunks.iter().enumerate() {
            let chunk_verifiers: Vec<_> = (&mut verifiers_it)
                .take(chunk.account_proofs.len())
                .collect();
            let mut even_verifier = Verifier::new(chunk_transcript(
                TXN_EVEN_LABEL,
                num_chunks,
                chunk_idx,
                &accounts_digest,
            )?);
            let mut odd_verifier = Verifier::new(chunk_transcript(
                TXN_ODD_LABEL,
                num_chunks,
                chunk_idx,
                &accounts_digest,
            )?);
            chunk.enforce_constraints_and_verify_only_sigma_protocols::<Parameters0, Parameters1>(
                chunk_verifiers,
                tree_root,
                account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                rmc.as_deref_mut(),
            )?;
            let r1cs_proof = chunk.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;
            let (even, odd) = get_verification_tuples_with_rng(
                even_verifier,
                odd_verifier,
                &r1cs_proof.even_proof,
                &r1cs_proof.odd_proof,
                rng,
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
        account_verifiers: Vec<AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>> + Clone,
        enc_gen: Affine<G0>,
    ) -> Result<()> {
        let (even_tuples, odd_tuples) = self
            .verify_and_return_tuples::<R, Parameters0, Parameters1>(
                rng,
                account_verifiers,
                tree_root,
                account_tree_params,
                account_comm_key,
                enc_gen,
                None,
            )?;
        batch_verify_bp(
            even_tuples,
            odd_tuples,
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::MultiAssetStateTransitionProofBatch;
    use crate::account::AccountStateTransitionProofBuilder;
    use crate::account::AccountStateTransitionProofVerifier;
    use crate::account::AccountTxnWitness;
    use crate::account::state_transition_multi::MultiAssetStateTransitionProof;
    use crate::account::tests::setup_multi_asset_settlement;
    use crate::util::{add_verification_tuples_batches_to_rmc, batch_verify_bp, verify_rmc};
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use ark_pallas::{Fr as PallasScalar, PallasConfig};
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use ark_vesta::{Fr as VestaScalar, VestaConfig};
    use curve_tree_relations::curve_tree::CurveTree;
    use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
    use std::time::Instant;

    type PallasParameters = PallasConfig;
    type VestaParameters = VestaConfig;

    struct Row {
        label: String,
        num_chunks: usize,
        prover_ms: f64,
        collect_tuples_ms: f64,
        batched_msm_ms: f64,
        /// collect_tuples + batched MSM (the `batch_verify_bp` path).
        verifier_batched_ms: f64,
        /// Full RandomizedMultChecker path: sigma + BP folded into one accumulator per curve.
        verifier_rmc_ms: f64,
        proof_bytes: usize,
    }

    fn ms(d: std::time::Duration) -> f64 {
        d.as_secs_f64() * 1000.0
    }

    #[test]
    fn multi_asset_chunked() {
        const ASSET_TREE_M: usize = 4;
        const ACCOUNT_TREE_M: usize = 8; // type-level multipath cap; allows g up to 8
        const NUM_GENS: usize = 1 << 17;
        const L: usize = 64;

        let num_legs = 20usize;
        let asset_tree_height = 4;
        let account_tree_height = 6;

        let (
            _asset_data_vec,
            _asset_paths,
            _asset_tree_root,
            _legs,
            leg_encs,
            _leg_enc_rands,
            alice_accounts,
            (sk_s, sk_s_e),
            bob_accounts,
            (_sk_r, _sk_r_e),
            _alice_paths,
            _bob_paths,
            account_tree_root,
            account_tree_params,
            _asset_tree_params,
            _asset_comm_params,
            account_comm_key,
            enc_gen,
        ) = setup_multi_asset_settlement::<NUM_GENS, L, ASSET_TREE_M, ACCOUNT_TREE_M>(
            num_legs,
            asset_tree_height,
            account_tree_height,
        );

        let mut rng = rand::thread_rng();
        let amount: u64 = 100;
        let nonce = b"mast_chunk_sweep_nonce";

        // Rebuild the account tree from the returned account states so we can regroup leaves
        // at any `g`. The leaf order matches the helper (Alice's accounts then Bob's), so the
        // rebuilt root must equal the returned one — assert it as a sanity check.
        let mut all_account_comms = Vec::with_capacity(2 * num_legs);
        for acc in &alice_accounts {
            all_account_comms.push(acc.commit(account_comm_key.clone()).unwrap().0);
        }
        for acc in &bob_accounts {
            all_account_comms.push(acc.commit(account_comm_key.clone()).unwrap().0);
        }
        let account_tree =
            CurveTree::<L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>::from_leaves(
                &all_account_comms,
                &account_tree_params,
                Some(account_tree_height),
            );
        assert_eq!(
            account_tree.root_node(),
            account_tree_root,
            "rebuilt account tree root must match the helper's"
        );

        // Alice's per-account updated states + commitments, built once.
        let mut alice_updated_comms = Vec::with_capacity(num_legs);
        let mut alice_updated_accounts = Vec::with_capacity(num_legs);
        for i in 0..num_legs {
            let updated = alice_accounts[i]
                .get_state_for_irreversible_send(amount)
                .unwrap();
            let updated_comm = updated.commit(account_comm_key.clone()).unwrap();
            alice_updated_comms.push(updated_comm);
            alice_updated_accounts.push(updated);
        }

        // N builders for Alice's accounts (indices 0..num_legs in the account tree). Rebuilt
        // per row because proving consumes them.
        let build_builders = || {
            let mut builders = Vec::with_capacity(num_legs);
            for i in 0..num_legs {
                let mut builder = AccountStateTransitionProofBuilder::<
                    L,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init(
                    AccountTxnWitness::new(
                        sk_s.0,
                        sk_s_e.0,
                        alice_accounts[i].clone(),
                        alice_updated_accounts[i].clone(),
                        alice_updated_comms[i],
                    ),
                    nonce,
                );
                builder.add_irreversible_send((
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                    amount,
                ));
                builders.push(builder);
            }
            builders
        };

        // Flat verifiers for all N accounts, in order, using the given nullifiers.
        let build_verifiers = |nullifiers: &[_]| {
            let mut verifiers = Vec::with_capacity(num_legs);
            for i in 0..num_legs {
                let mut verifier = AccountStateTransitionProofVerifier::<
                    L,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init(
                    alice_updated_comms[i], nullifiers[i], nonce
                );
                verifier.add_irreversible_send((
                    leg_encs[i].leg_enc_core_and_eph_keys.core.clone(),
                    leg_encs[i].leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ));
                verifiers.push(verifier);
            }
            verifiers
        };

        // Build `ceil(num_legs / g)` multipaths over Alice's leaves [0..num_legs), each
        // batching `g` leaves. One chunk per multipath ⇒ chunk size = g.
        let build_paths = |g: usize| {
            let alice_indices: Vec<u32> = (0..num_legs as u32).collect();
            let mut paths = Vec::new();
            for chunk in alice_indices.chunks(g) {
                paths.push(account_tree.get_paths_to_leaves(chunk).unwrap());
            }
            paths
        };

        println!(
            "\n=== MAST chunk-sweep: N={} independent per-asset accounts, L={}, M={}, height={} ===",
            num_legs, L, ACCOUNT_TREE_M, account_tree_height
        );
        println!("(chunk = one multipath; g = leaves per multipath = effective chunk size K)");

        let g_values: Vec<usize> = vec![1, 2, 4, ACCOUNT_TREE_M];

        let mut rows: Vec<Row> = Vec::new();

        // ---- Monolith baseline (g=M) ----
        {
            let builders = build_builders();
            let paths = build_paths(ACCOUNT_TREE_M);

            let t0 = Instant::now();
            let (proof, nullifiers) = MultiAssetStateTransitionProof::<
                L,
                ACCOUNT_TREE_M,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new::<_, PallasParams, VestaParams>(
                &mut rng,
                builders,
                paths,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();
            let prover_time = t0.elapsed();
            let proof_bytes = proof.compressed_size();

            let verifiers = build_verifiers(&nullifiers);

            let t0 = Instant::now();
            let (even_tuple, odd_tuple) = proof
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    verifiers,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
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
                account_tree_params.even_parameters.pc_gens(),
                account_tree_params.odd_parameters.pc_gens(),
                account_tree_params.even_parameters.bp_gens(),
                account_tree_params.odd_parameters.bp_gens(),
            )
            .unwrap();
            let batch_t = t0.elapsed();

            // RandomizedMultChecker path (MAST even=G0=Pallas, odd=G1=Vesta).
            let t0 = Instant::now();
            let mut rmc_even = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));
            let mut rmc_odd = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
            let verifiers_rmc = build_verifiers(&nullifiers);
            proof
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    verifiers_rmc,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
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
            let builders = build_builders();
            let paths = build_paths(g);

            let t0 = Instant::now();
            let batch = MultiAssetStateTransitionProofBatch::<
                L,
                ACCOUNT_TREE_M,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new::<_, PallasParams, VestaParams>(
                &mut rng,
                builders,
                paths,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();
            let prover_time = t0.elapsed();
            let proof_bytes = batch.total_proof_size();
            let num_chunks = batch.num_chunks();

            // Chunks are bound to their position in this batch.
            if g == 4 {
                let verify_chunks = |order: &[usize], rng: &mut rand::rngs::ThreadRng| {
                    let idxs: Vec<usize> = order.iter().flat_map(|&c| c * g..(c + 1) * g).collect();
                    let verifiers = idxs
                        .iter()
                        .map(|&i| build_verifiers(&batch.nullifiers).swap_remove(i))
                        .collect();
                    MultiAssetStateTransitionProofBatch {
                        chunks: order.iter().map(|&c| batch.chunks[c].clone()).collect(),
                        nullifiers: idxs.iter().map(|&i| batch.nullifiers[i]).collect(),
                        num_accounts: idxs.len() as u32,
                    }
                    .verify_batched_bp::<_, PallasParams, VestaParams>(
                        rng,
                        verifiers,
                        &account_tree_root,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_gen,
                    )
                };
                assert!(verify_chunks(&[0, 1, 2, 3, 4], &mut rng).is_ok());
                assert!(verify_chunks(&[1, 2, 3, 4], &mut rng).is_err());
                assert!(verify_chunks(&[1, 0, 2, 3, 4], &mut rng).is_err());
                assert!(verify_chunks(&[0, 0, 1, 2, 3, 4], &mut rng).is_err());
                let chunk_verifiers = (g..2 * g)
                    .map(|i| build_verifiers(&batch.nullifiers).swap_remove(i))
                    .collect();
                assert!(
                    batch.chunks[1]
                        .verify::<_, PallasParams, VestaParams>(
                            &mut rng,
                            chunk_verifiers,
                            &account_tree_root,
                            &account_tree_params,
                            account_comm_key.clone(),
                            enc_gen,
                            None,
                        )
                        .is_err()
                );
            }

            let verifiers = build_verifiers(&batch.nullifiers);

            let t0 = Instant::now();
            let (even_tuples, odd_tuples) = batch
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    &mut rng,
                    verifiers,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    None,
                )
                .unwrap();
            let collect_t = t0.elapsed();

            let t0 = Instant::now();
            batch_verify_bp(
                even_tuples,
                odd_tuples,
                account_tree_params.even_parameters.pc_gens(),
                account_tree_params.odd_parameters.pc_gens(),
                account_tree_params.even_parameters.bp_gens(),
                account_tree_params.odd_parameters.bp_gens(),
            )
            .unwrap();
            let batch_t = t0.elapsed();

            // RandomizedMultChecker path over all chunks.
            let t0 = Instant::now();
            let mut rmc_even = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));
            let mut rmc_odd = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
            let verifiers_rmc = build_verifiers(&batch.nullifiers);
            let (even_tuples, odd_tuples) = batch
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
                    &mut rng,
                    verifiers_rmc,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    Some(&mut rmc_even),
                )
                .unwrap();
            add_verification_tuples_batches_to_rmc(
                even_tuples,
                odd_tuples,
                account_tree_params.even_parameters.pc_gens(),
                account_tree_params.odd_parameters.pc_gens(),
                account_tree_params.even_parameters.bp_gens(),
                account_tree_params.odd_parameters.bp_gens(),
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
