//! PoC: chunked account registration.
//!
//! Experimental Same chunking idea as [`crate::leg::settlement_proof_chunked`], applied to account registration.

use crate::Error;
use crate::account::state::AccountStateCommitment;
use crate::account::{AccountCommitmentKeyTrait, AccountState};
use crate::account_registration::{REG_TXN_LABEL, RegTxnProof};
use crate::error::Result;
use crate::poseidon_impls::poseidon_2::params::Poseidon2Params;
use ark_ec::AffineRepr;
use ark_serialize::CanonicalSerialize;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use bulletproofs::r1cs::{Prover, R1CSProof, VerificationTuple, Verifier, batch_verify};
use bulletproofs::{BulletproofGens, PedersenGens};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use polymesh_dart_common::{AssetId, NullifierSkGenCounter};
use rand_core::CryptoRngCore;

/// One chunk: `K` registrations sharing a single prover and one `R1CSProof`.
#[derive(Clone, Debug)]
pub struct RegTxnProofChunk<
    G: AffineRepr,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    /// Per-registration sigma material; each has `partial.proof = None` (the BP proof is shared).
    pub regs: Vec<RegTxnProof<G, CHUNK_BITS, NUM_CHUNKS>>,
    /// One BP proof covering all registrations in the chunk.
    pub r1cs_proof: R1CSProof<G>,
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnProofChunk<G, CHUNK_BITS, NUM_CHUNKS>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk_affs: &[G::ScalarField],
        sk_encs: &[G::ScalarField],
        accounts: &[AccountState<G>],
        account_commitments: &[AccountStateCommitment<G>],
        rho_randomnesses: &[G::ScalarField],
        nonces: &[Vec<u8>],
        counter: NullifierSkGenCounter,
        account_comm_key: impl AccountCommitmentKeyTrait<G> + Clone,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut prover = Prover::new(leaf_level_pc_gens, transcript);
        let mut regs = Vec::with_capacity(accounts.len());
        // Optimz: Following can be parallelized by forking rng
        for i in 0..accounts.len() {
            let reg = RegTxnProof::new_with_given_prover(
                rng,
                sk_affs[i],
                sk_encs[i],
                &accounts[i],
                account_commitments[i].clone(),
                rho_randomnesses[i],
                counter,
                &nonces[i],
                account_comm_key.clone(),
                leaf_level_pc_gens,
                leaf_level_bp_gens,
                poseidon_config,
                T,
                &mut prover,
            )?;
            regs.push(reg);
        }
        let r1cs_proof = prover.prove_with_rng(leaf_level_bp_gens, rng)?;
        Ok(Self { regs, r1cs_proof })
    }

    /// Replay every registration's sigma protocol on one shared verifier, then extract the
    /// chunk's single BP verification tuple.
    pub fn verify_and_return_tuple<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        ids: &[G::ScalarField],
        pk_affs: &[G],
        pk_encs: &[G],
        asset_ids: &[AssetId],
        account_commitments: &[AccountStateCommitment<G>],
        nonces: &[Vec<u8>],
        counter: NullifierSkGenCounter,
        account_comm_key: impl AccountCommitmentKeyTrait<G> + Clone,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<VerificationTuple<G>> {
        let transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut verifier = Verifier::new(transcript);
        for i in 0..self.regs.len() {
            self.regs[i].verify_sigma_protocols_and_enforce_constraints(
                ids[i],
                pk_affs[i],
                pk_encs[i],
                asset_ids[i],
                &account_commitments[i],
                counter,
                &nonces[i],
                account_comm_key.clone(),
                leaf_level_pc_gens,
                leaf_level_bp_gens,
                poseidon_config,
                T,
                &mut verifier,
                rmc.as_deref_mut(),
            )?;
        }
        let tuple = verifier.verification_scalars_and_points_with_rng(&self.r1cs_proof, rng)?;
        Ok(tuple)
    }
}

/// A batch of account registrations as an ordered set of independent chunks, each its own
/// `R1CSProof`, batch-verified with a single `batch_verify` over all chunk tuples.
#[derive(Clone, Debug)]
pub struct RegTxnProofBatch<
    G: AffineRepr,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    pub chunks: Vec<RegTxnProofChunk<G, CHUNK_BITS, NUM_CHUNKS>>,
    pub num_regs: u32,
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnProofBatch<G, CHUNK_BITS, NUM_CHUNKS>
{
    /// Build the chunked registration: partition the `N` registrations into chunks of
    /// `chunk_size` (last chunk may be smaller), one `BPProof` per chunk.
    #[allow(clippy::too_many_arguments)]
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        chunk_size: usize,
        sk_affs: Vec<G::ScalarField>,
        sk_encs: Vec<G::ScalarField>,
        accounts: Vec<AccountState<G>>,
        account_commitments: Vec<AccountStateCommitment<G>>,
        rho_randomnesses: Vec<G::ScalarField>,
        nonces: Vec<Vec<u8>>,
        counter: NullifierSkGenCounter,
        account_comm_key: impl AccountCommitmentKeyTrait<G> + Clone,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<Self> {
        let num_regs = accounts.len();
        if num_regs == 0 {
            return Err(Error::ProofGenerationError(
                "At least one registration is required".to_string(),
            ));
        }
        if chunk_size == 0 {
            return Err(Error::ProofGenerationError(
                "chunk_size must be >= 1".to_string(),
            ));
        }
        if sk_affs.len() != num_regs
            || sk_encs.len() != num_regs
            || account_commitments.len() != num_regs
            || rho_randomnesses.len() != num_regs
            || nonces.len() != num_regs
        {
            return Err(Error::ProofGenerationError(
                "Mismatched per-registration input lengths".to_string(),
            ));
        }

        let mut chunks = Vec::with_capacity(num_regs.div_ceil(chunk_size));
        let mut start = 0;
        while start < num_regs {
            let end = (start + chunk_size).min(num_regs);
            let chunk = RegTxnProofChunk::new(
                rng,
                &sk_affs[start..end],
                &sk_encs[start..end],
                &accounts[start..end],
                &account_commitments[start..end],
                &rho_randomnesses[start..end],
                &nonces[start..end],
                counter,
                account_comm_key.clone(),
                leaf_level_pc_gens,
                leaf_level_bp_gens,
                poseidon_config,
                T,
            )?;
            chunks.push(chunk);
            start = end;
        }

        Ok(Self {
            chunks,
            num_regs: num_regs as u32,
        })
    }

    pub fn num_chunks(&self) -> usize {
        self.chunks.len()
    }

    pub fn total_proof_size(&self) -> usize {
        self.chunks
            .iter()
            .map(|c| {
                c.regs.iter().map(|r| r.compressed_size()).sum::<usize>()
                    + c.r1cs_proof.compressed_size()
            })
            .sum()
    }

    /// Run the per-chunk sigma-protocol verification and return one BP verification tuple per
    /// chunk.
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        ids: Vec<G::ScalarField>,
        pk_affs: Vec<G>,
        pk_encs: Vec<G>,
        asset_ids: Vec<AssetId>,
        account_commitments: Vec<AccountStateCommitment<G>>,
        nonces: Vec<Vec<u8>>,
        counter: NullifierSkGenCounter,
        account_comm_key: impl AccountCommitmentKeyTrait<G> + Clone,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<Vec<VerificationTuple<G>>> {
        let expected: usize = self.chunks.iter().map(|c| c.regs.len()).sum();
        if ids.len() != expected {
            return Err(Error::ProofVerificationError(
                "Number of public inputs does not match total registrations across chunks"
                    .to_string(),
            ));
        }

        let mut tuples = Vec::with_capacity(self.chunks.len());
        let mut start = 0;
        for chunk in &self.chunks {
            let end = start + chunk.regs.len();
            let tuple = chunk.verify_and_return_tuple(
                rng,
                &ids[start..end],
                &pk_affs[start..end],
                &pk_encs[start..end],
                &asset_ids[start..end],
                &account_commitments[start..end],
                &nonces[start..end],
                counter,
                account_comm_key.clone(),
                leaf_level_pc_gens,
                leaf_level_bp_gens,
                poseidon_config,
                T,
                rmc.as_deref_mut(),
            )?;
            tuples.push(tuple);
            start = end;
        }
        Ok(tuples)
    }

    /// Verify the whole batch with a single batched Bulletproofs check (`batch_verify`).
    pub fn verify_batched<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        ids: Vec<G::ScalarField>,
        pk_affs: Vec<G>,
        pk_encs: Vec<G>,
        asset_ids: Vec<AssetId>,
        account_commitments: Vec<AccountStateCommitment<G>>,
        nonces: Vec<Vec<u8>>,
        counter: NullifierSkGenCounter,
        account_comm_key: impl AccountCommitmentKeyTrait<G> + Clone,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<()> {
        let tuples = self.verify_and_return_tuples(
            rng,
            ids,
            pk_affs,
            pk_encs,
            asset_ids,
            account_commitments,
            nonces,
            counter,
            account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
            None,
        )?;
        batch_verify(tuples, leaf_level_pc_gens, leaf_level_bp_gens).map_err(Error::from)
    }
}

#[cfg(test)]
mod tests {
    use super::RegTxnProofBatch;
    use crate::account::{AccountCommitmentKeyTrait, AccountState};
    use crate::account_registration::tests::{setup_comm_key, test_params_for_poseidon2};
    use crate::keys::{keygen_enc, keygen_sig};
    use ark_pallas::Affine as PallasA;
    use ark_std::UniformRand;
    use bulletproofs::r1cs::add_verification_tuples_to_rmc;
    use curve_tree_relations::parameters::SelRerandProofParameters;
    use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
    use polymesh_dart_common::AssetId;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type Fr = ark_pallas::Fr;

    struct Row {
        label: String,
        num_chunks: usize,
        prover_ms: f64,
        collect_tuples_ms: f64,
        batched_msm_ms: f64,
        /// collect_tuples + batched MSM (the `batch_verify` path).
        verifier_batched_ms: f64,
        /// Full RandomizedMultChecker path: sigma + BP folded into one accumulator, one MSM.
        verifier_rmc_ms: f64,
        proof_bytes: usize,
    }

    fn ms(d: std::time::Duration) -> f64 {
        d.as_secs_f64() * 1000.0
    }

    #[test]
    fn registration_chunk() {
        // N independent registrations (with pk_T encryption, the meaty range-proof circuit).
        // Monolith = one BPProof over all N (chunk_size = N); chunked = smaller chunks,
        // batch-verified.
        const NUM_GENS: usize = 1 << 16;
        const CHUNK_BITS: usize = 48;
        const NUM_CHUNKS: usize = 6;

        let num_regs: usize = 20;
        let counter = 1;

        let mut rng = rand::thread_rng();

        let account_tree_params =
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();
        let pc_gens = account_tree_params.even_parameters.pc_gens();
        let bp_gens = account_tree_params.even_parameters.bp_gens();

        let account_comm_key = setup_comm_key(b"testing");
        let poseidon_params = test_params_for_poseidon2();

        // pk_T (force-transfer trusted party) → registration encrypts its randomness chunks.
        let enc_key_gen_T = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);
        let (_, pk_T) = keygen_enc(&mut rng, enc_key_gen_T);
        let T = Some((pk_T.0, enc_key_gen_T, enc_gen));

        // Build the N registrations once; every row reuses them. Only the chunking changes.
        let mut ids = Vec::with_capacity(num_regs);
        let mut sks = Vec::with_capacity(num_regs);
        let mut sk_encs = Vec::with_capacity(num_regs);
        let mut pks = Vec::with_capacity(num_regs);
        let mut pk_encs = Vec::with_capacity(num_regs);
        let mut accounts = Vec::with_capacity(num_regs);
        let mut account_comms = Vec::with_capacity(num_regs);
        let mut rho_randomnesses = Vec::with_capacity(num_regs);
        let mut asset_ids = Vec::with_capacity(num_regs);
        let mut nonces = Vec::with_capacity(num_regs);

        for i in 0..num_regs {
            let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let id = Fr::rand(&mut rng);
            let (sk_enc, pk_enc) = keygen_enc(&mut rng, account_comm_key.sk_enc_gen());
            let asset_id = (i + 1) as AssetId;
            let (account, rho_randomness) = AccountState::new(
                &mut rng,
                id,
                pk_i.0,
                pk_enc.0,
                asset_id,
                counter,
                poseidon_params.clone(),
            )
            .unwrap();
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            ids.push(id);
            sks.push(sk_i.0);
            sk_encs.push(sk_enc.0);
            pks.push(pk_i.0);
            pk_encs.push(pk_enc.0);
            accounts.push(account);
            account_comms.push(account_comm);
            rho_randomnesses.push(rho_randomness);
            asset_ids.push(asset_id);
            nonces.push(format!("reg_nonce_{}", i).into_bytes());
        }

        println!(
            "\n=== Registration chunk-sweep: N={} registrations, with pk_T, CHUNK_BITS={}, NUM_CHUNKS={} ===",
            num_regs, CHUNK_BITS, NUM_CHUNKS
        );
        println!("(single-curve; K = registrations per BPProof; K=N is the monolith)");

        // K=N (monolith) first, then progressively smaller chunks.
        let chunk_sizes: Vec<usize> = vec![num_regs, 10, 5, 2, 1];

        let mut rows: Vec<Row> = Vec::new();

        for &k in &chunk_sizes {
            let t0 = Instant::now();
            let batch = RegTxnProofBatch::<_, CHUNK_BITS, NUM_CHUNKS>::new(
                &mut rng,
                k,
                sks.clone(),
                sk_encs.clone(),
                accounts.clone(),
                account_comms.clone(),
                rho_randomnesses.clone(),
                nonces.clone(),
                counter,
                account_comm_key.clone(),
                &pc_gens,
                &bp_gens,
                &poseidon_params,
                T,
            )
            .unwrap();
            let prover_time = t0.elapsed();
            let proof_bytes = batch.total_proof_size();
            let num_chunks = batch.num_chunks();

            let t0 = Instant::now();
            let tuples = batch
                .verify_and_return_tuples(
                    &mut rng,
                    ids.clone(),
                    pks.clone(),
                    pk_encs.clone(),
                    asset_ids.clone(),
                    account_comms.clone(),
                    nonces.clone(),
                    counter,
                    account_comm_key.clone(),
                    &pc_gens,
                    &bp_gens,
                    &poseidon_params,
                    T,
                    None,
                )
                .unwrap();
            let collect_t = t0.elapsed();

            let t0 = Instant::now();
            bulletproofs::r1cs::batch_verify(tuples, &pc_gens, &bp_gens).unwrap();
            let batch_t = t0.elapsed();

            // RandomizedMultChecker path: fold sigma + every chunk's BP tuple into one
            // accumulator
            let t0 = Instant::now();
            let mut rmc = RandomizedMultChecker::new(Fr::rand(&mut rng));
            let tuples = batch
                .verify_and_return_tuples(
                    &mut rng,
                    ids.clone(),
                    pks.clone(),
                    pk_encs.clone(),
                    asset_ids.clone(),
                    account_comms.clone(),
                    nonces.clone(),
                    counter,
                    account_comm_key.clone(),
                    &pc_gens,
                    &bp_gens,
                    &poseidon_params,
                    T,
                    Some(&mut rmc),
                )
                .unwrap();
            add_verification_tuples_to_rmc(tuples, &pc_gens, &bp_gens, &mut rmc).unwrap();
            rmc.verify().unwrap();
            let rmc_t = t0.elapsed();

            rows.push(Row {
                label: if k == num_regs {
                    "monolith (K=N)".to_string()
                } else {
                    format!("chunked K={}", k)
                },
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
