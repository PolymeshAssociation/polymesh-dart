use crate::account_registration::{ENC_PK_LABEL, digits, powers_of_base};
use crate::add_to_transcript;
use crate::discrete_log::solve_discrete_log_bsgs;
use crate::error::*;
use crate::util::bp_gens_for_vec_commitment;
use crate::{NONCE_LABEL, TXN_CHALLENGE_LABEL};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, format, vec, vec::Vec};
use bulletproofs::r1cs::add_verification_tuple_to_rmc;
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSProof, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::ff::inner_product;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{Partial1PokPedersenCommitment, PartialPokDiscreteLog};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;

const ENC_KEY_DIST_LABEL: &'static [u8; 20] = b"enc_key_distribution";
const RECIPIENT_PK_LABEL: &'static [u8; 12] = b"recipient_pk";

/// Proof for distributing secret key to multiple recipients using Twisted ElGamal encryption.
/// The secret key `sk` is split into `NUM_CHUNKS` chunks of `CHUNK_BITS` bits each. For each chunk `sk_i`,
/// It has:
/// - Shared ciphertext: `C_i = enc_key_gen * r_i + enc_gen * sk_i` (for all recipients)
/// - Per-recipient ciphertext: `E_ji = recipient_pk_j * r_i` (one per recipient)
///
/// Each recipient `j` can decrypt by computing: `sk_i = C_i - (E_ji * sk_enc_inv_j) - enc_gen`
/// where `sk_enc_inv_j` is inverse of `j`-th recipient's decryption key
///
/// The proof ensures:
/// 1. Each chunk is in the correct range
/// 2. The same randomness `r_i` is used in both shared and recipient ciphertexts
/// 3. The chunks `sk_i` reconstruct to the claimed secret key `sk`
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct KeyDistributionProof<
    G: AffineRepr,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    /// Shared ciphertexts: `C_i = enc_key_gen * r_i + enc_gen * sk_i` for each chunk
    pub shared_cts: [G; NUM_CHUNKS],
    /// Per-recipient ciphertexts: `E_ji = recipient_pk_j * r_i` for each recipient j and chunk i
    pub recipient_cts: Vec<[G; NUM_CHUNKS]>,
    /// Proves `C_i = enc_key_gen * r_i + enc_gen * sk_i`. The response for `r_i` is reused in recipient proofs.
    pub resp_shared_cts: [Partial1PokPedersenCommitment<G>; NUM_CHUNKS],
    /// Proves `E_ji = recipient_pk_j * r_i` using the same `r_i` from `resp_enc_rands`
    pub resp_recipient_cts: Vec<[PartialPokDiscreteLog<G>; NUM_CHUNKS]>,
    /// Bulletproof vector commitment to all the chunks of the secret key
    pub comm_sk_chunks_bp: G,
    pub t_comm_sk_chunks_bp: G,
    /// For Pedersen commitment to the chunks. Ties with range proofs in Bulletproofs.
    pub resp_comm_sk_chunks_bp: SchnorrResponse<G>,
    /// Proves the chunks reconstruct to the full secret key committed in the combined ciphertext
    pub resp_combined_sk: PokPedersenCommitment<G>,
    pub resp_pk: PartialPokDiscreteLog<G>,
    pub proof: R1CSProof<G>,
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    KeyDistributionProof<G, CHUNK_BITS, NUM_CHUNKS>
{
    const CHECK_CHUNK_BITS: () = assert!(
        CHUNK_BITS <= 48
            && ((<G::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize + CHUNK_BITS - 1)
                / CHUNK_BITS
                == NUM_CHUNKS)
    );

    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        pk: G,
        recipient_pks: &[G],
        enc_key_gen: G,
        enc_gen: G,
        nonce: &[u8],
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
    ) -> Result<Self> {
        let _ = Self::CHECK_CHUNK_BITS;

        if recipient_pks.is_empty() {
            return Err(Error::NoRecipients);
        }

        let (sk_chunks, sk_chunks_u64) = digits::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>(sk);

        let mut transcript = MerlinTranscript::new(ENC_KEY_DIST_LABEL);
        add_to_transcript!(transcript, NONCE_LABEL, nonce, ENC_PK_LABEL, pk);
        for (i, &recipient_pk) in recipient_pks.iter().enumerate() {
            transcript.append_message(RECIPIENT_PK_LABEL, &(i as u64).to_le_bytes());
            recipient_pk.serialize_compressed(&mut transcript)?;
        }

        let mut shared_cts = [G::zero(); NUM_CHUNKS];
        let mut recipient_cts = vec![[G::zero(); NUM_CHUNKS]; recipient_pks.len()];
        let mut enc_rands = [G::ScalarField::zero(); NUM_CHUNKS];
        let mut enc_rands_blindings = [G::ScalarField::zero(); NUM_CHUNKS];
        let mut sk_chunks_blindings = [G::ScalarField::zero(); NUM_CHUNKS];

        let mut shared_cts_proto = Vec::with_capacity(NUM_CHUNKS);
        let mut recipient_cts_proto = vec![Vec::with_capacity(NUM_CHUNKS); recipient_pks.len()];

        let sk_blinding = G::ScalarField::rand(rng);

        for i in 0..NUM_CHUNKS {
            let r_i = G::ScalarField::rand(rng);
            enc_rands[i] = r_i;
            let r_i_blinding = G::ScalarField::rand(rng);
            enc_rands_blindings[i] = r_i_blinding;
            let sk_i_blinding = G::ScalarField::rand(rng);
            sk_chunks_blindings[i] = sk_i_blinding;

            // Shared ciphertext for chunk `ct = enc_key_gen * r_i + enc_gen * sk_i`
            let ct = (enc_key_gen * r_i + enc_gen * sk_chunks[i]).into_affine();
            shared_cts[i] = ct;

            // Prove `ct = enc_key_gen * r_i + enc_gen * sk_i`. The response for `r_i` will be reused in recipient proofs.
            let shared_proto = PokPedersenCommitmentProtocol::init(
                r_i,
                r_i_blinding,
                &enc_key_gen,
                sk_chunks[i],
                sk_i_blinding,
                &enc_gen,
            );
            shared_proto.challenge_contribution(&enc_key_gen, &enc_gen, &ct, &mut transcript)?;
            shared_cts_proto.push(shared_proto);

            // Per-recipient ciphertext for chunk i: E_ji = recipient_pk_j * r_i (one per recipient)
            // Prove each uses the same r_i (via partial proof that reuses r_i response from shared_proto)
            for (j, &recipient_pk) in recipient_pks.iter().enumerate() {
                let E_ji = (recipient_pk * r_i).into_affine();
                recipient_cts[j][i] = E_ji;

                let recipient_proto =
                    PokDiscreteLogProtocol::init(r_i, r_i_blinding, &recipient_pk);
                recipient_proto.challenge_contribution(&recipient_pk, &E_ji, &mut transcript)?;
                recipient_cts_proto[j].push(recipient_proto);
            }
        }

        let powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();
        let combined_enc_rand = inner_product(&enc_rands, &powers);

        let combined_s_proto = PokPedersenCommitmentProtocol::init(
            combined_enc_rand,
            G::ScalarField::rand(rng),
            &enc_key_gen,
            sk,
            sk_blinding,
            &enc_gen,
        );

        let combined_s_commitment = (enc_key_gen * combined_enc_rand + enc_gen * sk).into_affine();

        combined_s_proto.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &combined_s_commitment,
            &mut transcript,
        )?;

        let pk_proto = PokDiscreteLogProtocol::init(sk, sk_blinding, &enc_key_gen);
        pk_proto.challenge_contribution(&enc_key_gen, &pk, &mut transcript)?;

        let mut prover = Prover::new(&leaf_level_pc_gens, transcript);
        let comm_bp_blinding = G::ScalarField::rand(rng);
        let (comm_sk_chunks_bp, vars) =
            prover.commit_vec(&sk_chunks, comm_bp_blinding, &leaf_level_bp_gens);

        for (i, var) in vars.iter().enumerate() {
            range_proof(
                &mut prover,
                (*var).into(),
                Some(sk_chunks_u64[i] as u128),
                CHUNK_BITS,
            )?;
        }

        let mut gens = bp_gens_for_vec_commitment(NUM_CHUNKS as u32, &leaf_level_bp_gens);
        let mut bp_gens = Vec::with_capacity(NUM_CHUNKS + 1);
        bp_gens.push(leaf_level_pc_gens.B_blinding);
        for _ in 0..NUM_CHUNKS {
            bp_gens.push(gens.next().unwrap());
        }

        let mut blindings = vec![G::ScalarField::rand(rng)];
        blindings.extend_from_slice(&sk_chunks_blindings);
        let t_comm_sk_chunks_bp = SchnorrCommitment::new(&bp_gens, blindings);
        t_comm_sk_chunks_bp.challenge_contribution(&mut prover.transcript())?;

        let challenge = prover
            .transcript()
            .challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut resp_shared_cts = Vec::with_capacity(NUM_CHUNKS);
        let mut resp_recipient_cts = vec![Vec::with_capacity(NUM_CHUNKS); recipient_pks.len()];

        for s in shared_cts_proto {
            resp_shared_cts.push(s.gen_partial1_proof(&challenge));
        }
        for (i, r_vec) in recipient_cts_proto.into_iter().enumerate() {
            for r in r_vec {
                resp_recipient_cts[i].push(r.gen_partial_proof());
            }
        }

        let resp_combined_sk = combined_s_proto.gen_proof(&challenge);
        let resp_pk = pk_proto.gen_partial_proof();

        let mut wits = vec![comm_bp_blinding];
        wits.extend(sk_chunks);
        let resp_comm_sk_chunks_bp = t_comm_sk_chunks_bp.response(&wits, &challenge)?;
        Zeroize::zeroize(&mut wits);

        let proof = prover.prove_with_rng(leaf_level_bp_gens, rng)?;

        Ok(Self {
            shared_cts,
            recipient_cts,
            resp_shared_cts: resp_shared_cts.try_into().unwrap(),
            resp_recipient_cts: resp_recipient_cts
                .into_iter()
                .map(|v| v.try_into().unwrap())
                .collect(),
            comm_sk_chunks_bp,
            t_comm_sk_chunks_bp: t_comm_sk_chunks_bp.t,
            resp_comm_sk_chunks_bp,
            resp_combined_sk,
            resp_pk,
            proof,
        })
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        pk: &G,
        recipient_pks: &[G],
        enc_key_gen: G,
        enc_gen: G,
        nonce: &[u8],
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        if recipient_pks.is_empty() {
            return Err(Error::NoRecipients);
        }

        if self.recipient_cts.len() != recipient_pks.len() {
            return Err(Error::MismatchedRecipientCount);
        }

        let mut transcript = MerlinTranscript::new(ENC_KEY_DIST_LABEL);
        add_to_transcript!(transcript, NONCE_LABEL, nonce, ENC_PK_LABEL, pk);
        for (i, &recipient_pk) in recipient_pks.iter().enumerate() {
            transcript.append_message(RECIPIENT_PK_LABEL, &(i as u64).to_le_bytes());
            recipient_pk.serialize_compressed(&mut transcript)?;
        }

        for i in 0..NUM_CHUNKS {
            self.resp_shared_cts[i].challenge_contribution(
                &enc_key_gen,
                &enc_gen,
                &self.shared_cts[i],
                &mut transcript,
            )?;

            for j in 0..recipient_pks.len() {
                self.resp_recipient_cts[j][i].challenge_contribution(
                    &recipient_pks[j],
                    &self.recipient_cts[j][i],
                    &mut transcript,
                )?;
            }
        }

        let powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();

        let combined_cts = G::Group::msm(&self.shared_cts, &powers)
            .map_err(Error::size_mismatch)?
            .into_affine();
        self.resp_combined_sk.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &combined_cts,
            &mut transcript,
        )?;

        self.resp_pk
            .challenge_contribution(&enc_key_gen, &pk, &mut transcript)?;

        let mut verifier = Verifier::new(transcript);
        let vars = verifier.commit_vec(NUM_CHUNKS, self.comm_sk_chunks_bp);

        for var in vars {
            range_proof(&mut verifier, var.into(), None, CHUNK_BITS)?;
        }

        self.t_comm_sk_chunks_bp
            .serialize_compressed(&mut verifier.transcript())?;

        let challenge = verifier
            .transcript()
            .challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        for i in 0..NUM_CHUNKS {
            // Verify C_i = enc_key_gen * r_i + enc_gen * sk_i
            verify_or_rmc_3!(
                rmc,
                self.resp_shared_cts[i],
                format!("Shared ciphertext {} verification failed", i),
                self.shared_cts[i],
                enc_key_gen,
                enc_gen,
                &challenge,
                &self.resp_comm_sk_chunks_bp.0[i + 1],
            );

            // Verify each = recipient_pk_j * r_i uses the same r_i (from resp_enc_rands[i])
            for j in 0..recipient_pks.len() {
                verify_or_rmc_2!(
                    rmc,
                    self.resp_recipient_cts[j][i],
                    format!("Recipient {} ciphertext {} verification failed", j, i),
                    self.recipient_cts[j][i],
                    recipient_pks[j],
                    &challenge,
                    &self.resp_shared_cts[i].response1,
                );
            }
        }

        let mut gens = bp_gens_for_vec_commitment(NUM_CHUNKS as u32, &leaf_level_bp_gens);
        let mut bp_gens = Vec::with_capacity(NUM_CHUNKS + 1);
        bp_gens.push(leaf_level_pc_gens.B_blinding);
        for _ in 0..NUM_CHUNKS {
            bp_gens.push(gens.next().unwrap());
        }

        verify_schnorr_resp_or_rmc!(
            rmc,
            self.resp_comm_sk_chunks_bp,
            bp_gens,
            self.comm_sk_chunks_bp,
            self.t_comm_sk_chunks_bp,
            &challenge,
        );
        verify_or_rmc_3!(
            rmc,
            self.resp_combined_sk,
            "Combined ciphertext verification failed",
            combined_cts,
            enc_key_gen,
            enc_gen,
            &challenge,
        );
        verify_or_rmc_2!(
            rmc,
            self.resp_pk,
            "Public key verification failed",
            *pk,
            enc_key_gen,
            &challenge,
            &self.resp_combined_sk.response2,
        );

        match rmc.as_mut() {
            Some(rmc) => {
                let tuple = verifier.verification_scalars_and_points_with_rng(&self.proof, rng)?;
                add_verification_tuple_to_rmc(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens, rmc)
                    .map_err(|e| Error::from(e))
            }
            None => {
                verifier.verify_with_rng(
                    &self.proof,
                    leaf_level_pc_gens,
                    &leaf_level_bp_gens,
                    rng,
                )?;
                Ok(())
            }
        }
    }

    pub fn decrypt(
        &self,
        recipient_index: usize,
        sk_enc_inv: &G::ScalarField,
        enc_gen: G::Group,
    ) -> Result<G::ScalarField> {
        if recipient_index >= self.recipient_cts.len() {
            return Err(Error::InvalidRecipientIndex);
        }

        let max = 1_u64 << CHUNK_BITS;
        let chunks = self
            .shared_cts
            .iter()
            .enumerate()
            .map(|(i, &c)| {
                let eph_pk = self.recipient_cts[recipient_index][i];
                let enc_sk_i = c.into_group() - (eph_pk.into_group() * sk_enc_inv);
                solve_discrete_log_bsgs(max, enc_gen, enc_sk_i)
                    .map(|d| G::ScalarField::from(d))
                    .ok_or_else(|| Error::SolvingDiscreteLogFailed(i))
            })
            .collect::<Vec<_>>();

        let powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();
        let mut reconstructed = G::ScalarField::zero();
        for (i, c) in chunks.into_iter().enumerate() {
            reconstructed += c? * powers[i];
        }
        Ok(reconstructed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use ark_pallas::{Affine as PallasA, Fr as PallasFr};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use std::time::Instant;

    #[test]
    fn key_distribution_proof() {
        let mut rng = rand::thread_rng();

        const CHUNK_BITS: usize = 48;
        const NUM_CHUNKS: usize = 6;

        // Make sk small to run test faster
        let sk = PallasFr::from(u32::rand(&mut rng) as u64 + u16::rand(&mut rng) as u64);

        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);
        let pk = (enc_key_gen * sk).into_affine();

        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(512, 1);

        let nonce = b"test-nonce-enc-key-dist";

        println!("For 2 recipients");
        let mut recipient_sks_2 = Vec::new();
        let mut recipient_pks_2 = Vec::new();
        for _ in 0..2 {
            let recipient_sk = PallasFr::rand(&mut rng);
            recipient_sks_2.push(recipient_sk);
            recipient_pks_2.push((enc_key_gen * recipient_sk).into_affine());
        }

        let clock = Instant::now();
        let proof_2 = KeyDistributionProof::<PallasA, CHUNK_BITS, NUM_CHUNKS>::new(
            &mut rng,
            sk,
            pk,
            &recipient_pks_2,
            enc_key_gen,
            enc_gen,
            nonce,
            &pc_gens,
            &bp_gens,
        )
        .unwrap();
        let prover_time_2 = clock.elapsed();

        let clock = Instant::now();
        proof_2
            .verify(
                &mut rng,
                &pk,
                &recipient_pks_2,
                enc_key_gen,
                enc_gen,
                nonce,
                &pc_gens,
                &bp_gens,
                None,
            )
            .unwrap();
        let verifier_time_2_regular = clock.elapsed();

        let mut rmc = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let clock = Instant::now();
        proof_2
            .verify(
                &mut rng,
                &pk,
                &recipient_pks_2,
                enc_key_gen,
                enc_gen,
                nonce,
                &pc_gens,
                &bp_gens,
                Some(&mut rmc),
            )
            .unwrap();
        assert!(rmc.verify());
        let verifier_time_2_rmc = clock.elapsed();

        for (i, recipient_sk) in recipient_sks_2.iter().enumerate() {
            let decrypted = proof_2
                .decrypt(i, &recipient_sk.inverse().unwrap(), enc_gen.into_group())
                .unwrap();
            assert_eq!(sk, decrypted);
        }

        println!("total proof size = {}", proof_2.compressed_size());
        println!("total prover time = {:?}", prover_time_2);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_2_regular, verifier_time_2_rmc
        );

        println!("For 3 recipients");
        let mut recipient_sks_3 = Vec::new();
        let mut recipient_pks_3 = Vec::new();
        for _ in 0..3 {
            let recipient_sk = PallasFr::rand(&mut rng);
            recipient_sks_3.push(recipient_sk);
            recipient_pks_3.push((enc_key_gen * recipient_sk).into_affine());
        }

        let clock = Instant::now();
        let proof_3 = KeyDistributionProof::<PallasA, CHUNK_BITS, NUM_CHUNKS>::new(
            &mut rng,
            sk,
            pk,
            &recipient_pks_3,
            enc_key_gen,
            enc_gen,
            nonce,
            &pc_gens,
            &bp_gens,
        )
        .unwrap();
        let prover_time_3 = clock.elapsed();

        let clock = Instant::now();
        proof_3
            .verify(
                &mut rng,
                &pk,
                &recipient_pks_3,
                enc_key_gen,
                enc_gen,
                nonce,
                &pc_gens,
                &bp_gens,
                None,
            )
            .unwrap();
        let verifier_time_3_regular = clock.elapsed();

        // Verify with RandomizedMultChecker
        let mut rmc = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let clock = Instant::now();
        proof_3
            .verify(
                &mut rng,
                &pk,
                &recipient_pks_3,
                enc_key_gen,
                enc_gen,
                nonce,
                &pc_gens,
                &bp_gens,
                Some(&mut rmc),
            )
            .unwrap();
        assert!(rmc.verify());
        let verifier_time_3_rmc = clock.elapsed();

        for (i, recipient_sk) in recipient_sks_3.iter().enumerate() {
            let decrypted = proof_3
                .decrypt(i, &recipient_sk.inverse().unwrap(), enc_gen.into_group())
                .unwrap();
            assert_eq!(sk, decrypted);
        }

        println!("total proof size = {}", proof_3.compressed_size());
        println!("total prover time = {:?}", prover_time_3);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_3_regular, verifier_time_3_rmc
        );
    }
}
