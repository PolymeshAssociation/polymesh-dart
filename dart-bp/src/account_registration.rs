use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, TXN_CHALLENGE_LABEL,
    TXN_INSTANCE_LABEL,
};
use crate::error::*;
use crate::poseidon_impls::poseidon_2::{Poseidon_hash_2_constraints_simple, Poseidon2Params};
use crate::util::bp_gens_for_vec_commitment;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::BigInteger;
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, vec, vec::Vec};
use ark_std::{format, string::ToString};
use bulletproofs::r1cs::{
    ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, Verifier,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::curve::curve_check;
use curve_tree_relations::lookup::Lookup3Bit;
use curve_tree_relations::range_proof::range_proof;
use curve_tree_relations::rerandomize::scalar_mult;
use dock_crypto_utils::elgamal::Ciphertext;
use dock_crypto_utils::ff::inner_product;
use dock_crypto_utils::msm::WindowTable;
use dock_crypto_utils::solve_discrete_log::solve_discrete_log_bsgs;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, NullifierSkGenCounter};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};

/// Proof of encrypted randomness
// TODO: Check if i can use Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf).
// The problem is that response of all chunks is aggregated in one value so tying it with BP is not straightforward. So need to check if aggregating
// those responses and comparing is safe
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EncryptedRandomness<
    G: AffineRepr,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    pub ciphertexts: [Ciphertext<G>; NUM_CHUNKS],
    /// For relation `g * r_i`
    pub resp_eph_pk: [PokDiscreteLog<G>; NUM_CHUNKS],
    /// For relation `pk_T * r_i + h * s_i`
    pub resp_encrypted: [PokPedersenCommitment<G>; NUM_CHUNKS],
    /// Bulletproof vector commitment to all the chunks of randomness
    pub comm_s_chunks_bp: G,
    pub t_comm_s_chunks_bp: G,
    pub resp_comm_s_chunks_bp: SchnorrResponse<G>,
    /// For Pedersen commitment to the weighted randomness and chunks. The weighted chunks equals the account commitment randomness
    pub resp_combined_s: PokPedersenCommitment<G>,
}

/// This is the proof for user registering its (signing) public key for an asset. Report section 5.1.3, called "Account Registration"
/// We could register both signing and encryption keys by modifying this proof even though the encryption isn't used in account commitment.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RegTxnProof<G: AffineRepr, const CHUNK_BITS: usize = 48, const NUM_CHUNKS: usize = 6> {
    pub resp_acc_comm: PokPedersenCommitment<G>,
    pub resp_initial_nullifier: PokDiscreteLog<G>,
    /// Called `N` in the report. This helps during account freezing to remove `g_i * rho` term from account state commitment.
    pub initial_nullifier: G,
    /// Bulletproof vector commitment to `sk, initial_rho, current_rho`
    pub comm_rho_bp: G,
    pub t_comm_rho_bp: G,
    pub resp_comm_rho_bp: SchnorrResponse<G>,
    pub resp_pk: PokDiscreteLog<G>,
    /// Called `uppercase Omega` in the report
    pub encrypted_randomness: Option<EncryptedRandomness<G, CHUNK_BITS, NUM_CHUNKS>>,
    pub proof: R1CSProof<G>,
}

const REG_TXN_LABEL: &'static [u8; 12] = b"registration";

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnProof<G, CHUNK_BITS, NUM_CHUNKS>
{
    // ceil(MODULUS_BIT_SIZE/CHUNK_BITS) == NUM_CHUNKS
    const CHECK_CHUNK_BITS: () = assert!(
        CHUNK_BITS <= 48
            && ((<G::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize + CHUNK_BITS - 1)
                / CHUNK_BITS
                == NUM_CHUNKS)
    );

    /// `T` are the public key `pk_T`, generator used when creating key `pk_T` and the generator used to encrypt randomness chunk.
    /// This is intentionally kept different from the generator for randomness in account commitment to prevent anyone from
    /// learning the next nullifier
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        // poseidon_config: &PoseidonConfig<G::ScalarField>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<Self> {
        let _ = Self::CHECK_CHUNK_BITS;
        if account.balance != 0 {
            return Err(Error::ProofOfBalanceError(
                "Balance must be 0 for registration".to_string(),
            ));
        }
        if account.counter != 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be 0 for registration".to_string(),
            ));
        }
        debug_assert_eq!(account.rho.square(), account.current_rho);

        // Need to prove that:
        // 1. rho is generated correctly and current_rho = rho^2
        // 2. balance is 0
        // 3. counter is 0
        // 4. Knowledge of randomness
        // 5. if T is provided, prove that randomness is encrypted correctly for pk_T

        let mut transcript = MerlinTranscript::new(REG_TXN_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        account.asset_id.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        let initial_nullifier = account.initial_nullifier(&account_comm_key);

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // D = pk + g_k * asset_id + g_l * id
        let D = pk.into_group()
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(account.asset_id))
            + (account_comm_key.id_gen() * account.id);

        let sk_blinding = G::ScalarField::rand(rng);
        let rho_blinding = G::ScalarField::rand(rng);
        let current_rho_blinding = G::ScalarField::rand(rng);
        let s_blinding = G::ScalarField::rand(rng);

        // For proving Comm - D - initial_nullifier = g_i * rho^2 + g_j * s
        let comm_protocol = PokPedersenCommitmentProtocol::init(
            account.current_rho,
            current_rho_blinding,
            &account_comm_key.current_rho_gen(),
            account.randomness,
            s_blinding,
            &account_comm_key.randomness_gen(),
        );
        let reduced_acc_comm =
            (account_commitment.0.into_group() - D - initial_nullifier.into_group()).into_affine();
        comm_protocol.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;

        // For proving initial_nullifier
        let init_null_protocol =
            PokDiscreteLogProtocol::init(account.rho, rho_blinding, &account_comm_key.rho_gen());
        init_null_protocol.challenge_contribution(
            &account_comm_key.rho_gen(),
            &initial_nullifier,
            &mut transcript,
        )?;

        // TODO: Try combining all these into 1 eq by RLC. Bases need to be adapted accordingly so it might not lead to that performant solution
        // Break randomness `s` in `NUM_CHUNKS` chunks and encrypt each chunk using exponent Elgamal. Then initialize sigma
        // protocols for proving correctness of each ciphertext
        let enc_prep = if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            let (s_chunks, s_chunks_as_u64) =
                digits::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>(account.randomness);
            let table = WindowTable::new(NUM_CHUNKS, enc_gen.into_group());

            // encs[i] = h * s_chunks[i]
            let encs = G::Group::normalize_batch(&table.multiply_many(&s_chunks));

            let enc_rands = (0..NUM_CHUNKS)
                .map(|_| G::ScalarField::rand(rng))
                .collect::<Vec<_>>();

            let s_chunks_blindings = (0..NUM_CHUNKS)
                .map(|_| G::ScalarField::rand(rng))
                .collect::<Vec<_>>();
            let enc_rands_blindings = (0..NUM_CHUNKS)
                .map(|_| G::ScalarField::rand(rng))
                .collect::<Vec<_>>();

            let ciphertexts = (0..NUM_CHUNKS)
                .map(|i| {
                    Ciphertext::new_given_randomness(&encs[i], &enc_rands[i], pk_T, enc_key_gen)
                })
                .collect::<Vec<_>>();

            // For proving r_i in g * r_i = ct_i.0
            let mut eph_proto = Vec::with_capacity(NUM_CHUNKS);
            // For proving r_i, s_i in pk_T * r_i + h * s_i = ct_i.1
            let mut enc_proto = Vec::with_capacity(NUM_CHUNKS);

            for i in 0..NUM_CHUNKS {
                eph_proto.push(PokDiscreteLogProtocol::init(
                    enc_rands[i],
                    enc_rands_blindings[i],
                    enc_key_gen,
                ));
                eph_proto[i].challenge_contribution(
                    &enc_key_gen,
                    &ciphertexts[i].eph_pk,
                    &mut transcript,
                )?;

                enc_proto.push(PokPedersenCommitmentProtocol::init(
                    enc_rands[i],
                    enc_rands_blindings[i],
                    pk_T,
                    s_chunks[i],
                    s_chunks_blindings[i],
                    enc_gen,
                ));
                enc_proto[i].challenge_contribution(
                    pk_T,
                    enc_gen,
                    &ciphertexts[i].encrypted,
                    &mut transcript,
                )?;
            }

            Some((
                s_chunks,
                s_chunks_as_u64,
                enc_rands,
                ciphertexts,
                s_chunks_blindings,
                eph_proto,
                enc_proto,
            ))
        } else {
            None
        };

        let mut prover = Prover::new(&leaf_level_pc_gens, transcript);

        // NOTE: We can save 2 group elements in total by committing all variables (including chunks) in
        // a single commitment. It complicates the implementation a bit

        let com_rho_bp_blinding = G::ScalarField::rand(rng);
        let (comm_rho_bp, vars) = prover.commit_vec(
            &[account.sk, account.rho, account.current_rho],
            com_rho_bp_blinding,
            &leaf_level_bp_gens,
        );
        Self::enforce_constraints(
            &mut prover,
            account.asset_id,
            counter,
            vars,
            poseidon_config,
        )?;

        let t_comm_rho_bp = SchnorrCommitment::new(
            &Self::bp_gens_for_comm_rho(leaf_level_pc_gens, leaf_level_bp_gens),
            vec![
                G::ScalarField::rand(rng),
                sk_blinding,
                rho_blinding,
                current_rho_blinding,
            ],
        );

        let t_pk =
            PokDiscreteLogProtocol::init(account.sk, sk_blinding, &account_comm_key.sk_gen());

        // Commit to each chunk of randomness and prove that each chunk in range using BP
        let (comm_s_chunks_bp, com_s_bp_blinding) =
            if let Some((s_chunks, s_chunks_as_u64, _, _, _, _, _)) = &enc_prep {
                let com_s_bp_blinding = G::ScalarField::rand(rng);
                let (comm_s_bp, vars) =
                    prover.commit_vec(s_chunks, com_s_bp_blinding, &leaf_level_bp_gens);
                for (i, var) in vars.into_iter().enumerate() {
                    range_proof(
                        &mut prover,
                        var.into(),
                        Some(s_chunks_as_u64[i]),
                        CHUNK_BITS,
                    )?;
                }
                (Some(comm_s_bp), Some(com_s_bp_blinding))
            } else {
                (None, None)
            };

        let mut transcript_ref = prover.transcript();

        t_comm_rho_bp.challenge_contribution(&mut transcript_ref)?;
        t_pk.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript_ref)?;

        // Take challenge contribution of ciphertext of each chunk
        let (t_comm_s_chunks_bp, combined_s_proto) =
            if let Some((_, _, enc_rands, _, s_chunks_blindings, _, _)) = &enc_prep {
                let mut blindings = vec![G::ScalarField::rand(rng)];
                for i in 0..NUM_CHUNKS {
                    blindings.push(s_chunks_blindings[i]);
                }
                let t_comm_s_chunks_bp = SchnorrCommitment::new(
                    &Self::bp_gens_for_comm_s_chunks(leaf_level_pc_gens, leaf_level_bp_gens),
                    blindings,
                );
                t_comm_s_chunks_bp.challenge_contribution(&mut transcript_ref)?;

                let powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();
                let combined_enc_rand = inner_product::<G::ScalarField>(enc_rands, &powers);
                let pk_T = T.as_ref().unwrap().0;
                let h = T.as_ref().unwrap().2;
                let combined_s_commitment =
                    (pk_T * combined_enc_rand + h * account.randomness).into_affine();

                let combined_s_proto = PokPedersenCommitmentProtocol::init(
                    combined_enc_rand,
                    G::ScalarField::rand(rng),
                    &pk_T,
                    account.randomness,
                    s_blinding,
                    &h,
                );
                combined_s_proto.challenge_contribution(
                    &pk_T,
                    &h,
                    &combined_s_commitment,
                    &mut transcript_ref,
                )?;

                (Some(t_comm_s_chunks_bp), Some(combined_s_proto))
            } else {
                (None, None)
            };

        let prover_challenge =
            transcript_ref.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let resp_comm = comm_protocol.gen_proof(&prover_challenge);
        let resp_initial_nullifier = init_null_protocol.gen_proof(&prover_challenge);

        let resp_comm_rho_bp = t_comm_rho_bp.response(
            &[
                com_rho_bp_blinding,
                account.sk,
                account.rho,
                account.current_rho,
            ],
            &prover_challenge,
        )?;
        let resp_pk = t_pk.gen_proof(&prover_challenge);

        let encrypted_randomness = if let Some((
            s_chunks,
            _,
            _,
            ciphertexts,
            _,
            mut eph_proto,
            mut enc_proto,
        )) = enc_prep
        {
            let comm_s_chunks_bp = comm_s_chunks_bp.unwrap();
            let mut resp_eph_pk = Vec::with_capacity(NUM_CHUNKS);
            let mut resp_encrypted = Vec::with_capacity(NUM_CHUNKS);
            let mut wits = vec![com_s_bp_blinding.unwrap()];
            for s_chunk in s_chunks.into_iter() {
                let eph = eph_proto.remove(0);
                resp_eph_pk.push(eph.gen_proof(&prover_challenge));
                let enc = enc_proto.remove(0);
                resp_encrypted.push(enc.gen_proof(&prover_challenge));
                wits.push(s_chunk);
            }

            let t_comm_s_chunks_bp = t_comm_s_chunks_bp.unwrap();
            let resp_comm_s_chunks_bp = t_comm_s_chunks_bp.response(&wits, &prover_challenge)?;
            let resp_combined_s = combined_s_proto.unwrap().gen_proof(&prover_challenge);

            Some(EncryptedRandomness::<G, CHUNK_BITS, NUM_CHUNKS> {
                ciphertexts: ciphertexts.try_into().unwrap(),
                resp_eph_pk: resp_eph_pk.try_into().unwrap(),
                resp_encrypted: resp_encrypted.try_into().unwrap(),
                comm_s_chunks_bp,
                t_comm_s_chunks_bp: t_comm_s_chunks_bp.t,
                resp_comm_s_chunks_bp,
                resp_combined_s,
            })
        } else {
            None
        };

        let proof = prover.prove_with_rng(leaf_level_bp_gens, rng)?;

        Ok(Self {
            resp_acc_comm: resp_comm,
            resp_initial_nullifier,
            t_comm_rho_bp: t_comm_rho_bp.t,
            resp_comm_rho_bp,
            resp_pk,
            comm_rho_bp,
            initial_nullifier,
            encrypted_randomness,
            proof,
        })
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        id: G::ScalarField,
        pk: &G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        // poseidon_config: &PoseidonConfig<G::ScalarField>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<()> {
        let _ = Self::CHECK_CHUNK_BITS;
        if T.is_none() ^ self.encrypted_randomness.is_none() {
            return Err(Error::PkTAndEncryptedRandomnessInconsistent);
        }
        if self.resp_comm_rho_bp.len() != 4 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                4,
                self.resp_comm_rho_bp.len(),
            ));
        }
        if let Some(enc_rand) = &self.encrypted_randomness {
            if enc_rand.resp_comm_s_chunks_bp.len() != (NUM_CHUNKS + 1) {
                return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                    NUM_CHUNKS + 1,
                    enc_rand.resp_comm_s_chunks_bp.len(),
                ));
            }
        }

        let mut verifier_transcript = MerlinTranscript::new(REG_TXN_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        asset_id.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        verifier_transcript
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // D = pk + g_k * asset_id + g_l * id
        let D = pk.into_group()
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id))
            + (account_comm_key.id_gen() * id);

        let reduced_acc_comm =
            (account_commitment.0.into_group() - D - self.initial_nullifier.into_group())
                .into_affine();
        self.resp_acc_comm.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut verifier_transcript,
        )?;

        self.resp_initial_nullifier.challenge_contribution(
            &account_comm_key.rho_gen(),
            &self.initial_nullifier,
            &mut verifier_transcript,
        )?;

        // Take challenge contribution of ciphertext of each chunk
        if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            let enc_rand = self.encrypted_randomness.as_ref().unwrap();
            for i in 0..NUM_CHUNKS {
                enc_rand.resp_eph_pk[i].challenge_contribution(
                    enc_key_gen,
                    &enc_rand.ciphertexts[i].eph_pk,
                    &mut verifier_transcript,
                )?;
                enc_rand.resp_encrypted[i].challenge_contribution(
                    pk_T,
                    enc_gen,
                    &enc_rand.ciphertexts[i].encrypted,
                    &mut verifier_transcript,
                )?;
            }
        }

        let mut verifier = Verifier::new(verifier_transcript);

        let vars = verifier.commit_vec(3, self.comm_rho_bp);
        Self::enforce_constraints(&mut verifier, asset_id, counter, vars, poseidon_config)?;

        // Check if each chunk is in range
        if let Some(enc_rand) = &self.encrypted_randomness {
            let mut vars = verifier.commit_vec(NUM_CHUNKS, enc_rand.comm_s_chunks_bp);
            for _ in 0..NUM_CHUNKS {
                range_proof(&mut verifier, vars.remove(0).into(), None, CHUNK_BITS)?;
            }
        }

        let mut transcript_ref = verifier.transcript();

        self.t_comm_rho_bp
            .serialize_compressed(&mut transcript_ref)?;
        self.resp_pk.challenge_contribution(
            &account_comm_key.sk_gen(),
            &pk,
            &mut transcript_ref,
        )?;

        let combined_s_commitment = if let Some(enc_rand) = &self.encrypted_randomness {
            enc_rand
                .t_comm_s_chunks_bp
                .serialize_compressed(&mut transcript_ref)?;

            let powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();
            let encs = enc_rand
                .ciphertexts
                .iter()
                .map(|c| c.encrypted)
                .collect::<Vec<_>>();
            let combined_s_commitment = G::Group::msm(&encs, &powers)
                .map_err(Error::size_mismatch)?
                .into_affine();

            let pk_T = T.as_ref().unwrap().0;
            let h = T.as_ref().unwrap().2;
            enc_rand.resp_combined_s.challenge_contribution(
                &pk_T,
                &h,
                &combined_s_commitment,
                &mut transcript_ref,
            )?;
            Some(combined_s_commitment)
        } else {
            None
        };

        let verifier_challenge =
            transcript_ref.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        if !self.resp_acc_comm.verify(
            &reduced_acc_comm,
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Account commitment verification failed".to_string(),
            ));
        }

        if !self.resp_initial_nullifier.verify(
            &self.initial_nullifier,
            &account_comm_key.rho_gen(),
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Initial nullifier verification failed".to_string(),
            ));
        }

        self.resp_comm_rho_bp.is_valid(
            &Self::bp_gens_for_comm_rho(leaf_level_pc_gens, leaf_level_bp_gens),
            &self.comm_rho_bp,
            &self.t_comm_rho_bp,
            &verifier_challenge,
        )?;

        if !self
            .resp_pk
            .verify(pk, &account_comm_key.sk_gen(), &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "Public key verification failed".to_string(),
            ));
        }

        if self.resp_comm_rho_bp.0[1] != self.resp_pk.response {
            return Err(Error::ProofVerificationError(
                "Secret key mismatch between BP commitment and public key".to_string(),
            ));
        }
        if self.resp_comm_rho_bp.0[2] != self.resp_initial_nullifier.response {
            return Err(Error::ProofVerificationError(
                "Initial rho mismatch between BP commitment and initial nullifier".to_string(),
            ));
        }
        if self.resp_comm_rho_bp.0[3] != self.resp_acc_comm.response1 {
            return Err(Error::ProofVerificationError(
                "Rho mismatch between account and BP commitment".to_string(),
            ));
        }

        if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            // unwrap is fine as its already checked in the beginning
            let enc_rand = self.encrypted_randomness.as_ref().unwrap();
            for i in 0..NUM_CHUNKS {
                if !enc_rand.resp_eph_pk[i].verify(
                    &enc_rand.ciphertexts[i].eph_pk,
                    enc_key_gen,
                    &verifier_challenge,
                ) {
                    return Err(Error::ProofVerificationError(
                        "Encrypted randomness verification failed".to_string(),
                    ));
                }
                if !enc_rand.resp_encrypted[i].verify(
                    &enc_rand.ciphertexts[i].encrypted,
                    pk_T,
                    enc_gen,
                    &verifier_challenge,
                ) {
                    return Err(Error::ProofVerificationError(
                        "Encrypted randomness verification failed".to_string(),
                    ));
                }

                if enc_rand.resp_eph_pk[i].response != enc_rand.resp_encrypted[i].response1 {
                    return Err(Error::ProofVerificationError(
                        "Mismatch in combined encryption randomness".to_string(),
                    ));
                }

                if enc_rand.resp_comm_s_chunks_bp.0[i + 1] != enc_rand.resp_encrypted[i].response2 {
                    return Err(Error::ProofVerificationError(format!(
                        "Mismatch in {i}-th commitment randomness chunk"
                    )));
                }
            }

            enc_rand.resp_comm_s_chunks_bp.is_valid(
                &Self::bp_gens_for_comm_s_chunks(leaf_level_pc_gens, leaf_level_bp_gens),
                &enc_rand.comm_s_chunks_bp,
                &enc_rand.t_comm_s_chunks_bp,
                &verifier_challenge,
            )?;

            if !enc_rand.resp_combined_s.verify(
                &combined_s_commitment.unwrap(),
                pk_T,
                enc_gen,
                &verifier_challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    "Combined randomness verification failed".to_string(),
                ));
            }

            if enc_rand.resp_combined_s.response2 != self.resp_acc_comm.response2 {
                return Err(Error::ProofVerificationError(
                    "Mismatch in commitment randomness".to_string(),
                ));
            }
        }

        verifier.verify_with_rng(&self.proof, leaf_level_pc_gens, &leaf_level_bp_gens, rng)?;
        Ok(())
    }

    fn enforce_constraints<CS: ConstraintSystem<G::ScalarField>>(
        cs: &mut CS,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        mut vars: Vec<Variable<G::ScalarField>>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
    ) -> Result<()> {
        let var_sk = vars.remove(0);
        let var_rho = vars.remove(0);
        let var_rho_sq = vars.remove(0);

        let lc_rho: LinearCombination<G::ScalarField> = var_rho.into();
        let combined = AccountState::<G>::concat_asset_id_counter(asset_id, counter);
        let c = LinearCombination::from(combined);
        let lc_rho_1 = Poseidon_hash_2_constraints_simple(cs, var_sk.into(), c, poseidon_config)?;
        let (_, _, var_rho_sq_1) = cs.multiply(lc_rho.clone(), lc_rho.clone());
        cs.constrain(lc_rho_1 - lc_rho);
        cs.constrain(var_rho_sq_1 - var_rho_sq);
        Ok(())
    }

    fn bp_gens_for_comm_rho(
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
    ) -> [G; 4] {
        let mut gens = bp_gens_for_vec_commitment(3, leaf_level_bp_gens);
        [
            leaf_level_pc_gens.B_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ]
    }

    // fn bp_gens_for_comm_s_chunks(leaf_level_pc_gens: &PedersenGens<G>, leaf_level_bp_gens: &BulletproofGens<G>) -> [G; NUM_CHUNKS + 1] {
    //     let mut g = [leaf_level_pc_gens.B_blinding; NUM_CHUNKS + 1];
    //     let mut gens = bp_gens_for_vec_commitment(NUM_CHUNKS, leaf_level_bp_gens);
    //     for i in 0..NUM_CHUNKS {
    //         g[i+1] = gens.next().unwrap();
    //     }
    //     g
    // }
    fn bp_gens_for_comm_s_chunks(
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
    ) -> Vec<G> {
        let mut g = Vec::with_capacity(NUM_CHUNKS + 1);
        g.push(leaf_level_pc_gens.B_blinding);
        let mut gens = bp_gens_for_vec_commitment(NUM_CHUNKS, leaf_level_bp_gens);
        for _ in 0..NUM_CHUNKS {
            g.push(gens.next().unwrap());
        }
        g
    }
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    EncryptedRandomness<G, CHUNK_BITS, NUM_CHUNKS>
{
    pub fn decrypt(&self, sk_T: &G::ScalarField, enc_gen: G::Group) -> Result<G::ScalarField> {
        let max = 1_u64 << CHUNK_BITS;
        let chunks = self
            .ciphertexts
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let e = c.decrypt(sk_T).into_group();
                // TODO: This can be optimized as discrete log with same base is being computed
                solve_discrete_log_bsgs(max, enc_gen, e)
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

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RegTxnProofAlt<
    G0: SWCurveConfig + Clone + Copy,
    G1: SWCurveConfig<ScalarField = G0::BaseField, BaseField = G0::ScalarField> + Clone + Copy,
> {
    pub T_1: Affine<G1>,
    pub T_2: Affine<G1>,
    pub resp_comm: PokPedersenCommitment<Affine<G0>>,
    pub resp_initial_nullifier: PokDiscreteLog<Affine<G0>>,
    pub comm_bp: Affine<G0>,
    /// Called `N` in the report. This helps during account freezing to remove `g_i * rho` term from account state commitment.
    pub initial_nullifier: Affine<G0>,
    pub t_comm_bp: Affine<G0>,
    pub resp_comm_bp: SchnorrResponse<Affine<G0>>,
    pub resp_pk: PokDiscreteLog<Affine<G0>>,
    pub resp_T_1: PokDiscreteLog<Affine<G1>>,
    pub resp_T_2: PokDiscreteLog<Affine<G1>>,
    pub proof: R1CSProof<Affine<G0>>,
}

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> RegTxnProofAlt<G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: Affine<G0>,
        account: &AccountState<Affine<G0>>,
        account_commitment: AccountStateCommitment<Affine<G0>>,
        r_1: F1,
        r_2: F1,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        pk_T: Affine<G1>,
        pk_T_gen: Affine<G1>,
        pk_T_gen_tables: &[Lookup3Bit<2, F0>],
        leaf_level_pc_gens: &PedersenGens<Affine<G0>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G0>>,
    ) -> Result<Self> {
        if account.balance != 0 {
            return Err(Error::ProofOfBalanceError(
                "Balance must be 0 for registration".to_string(),
            ));
        }
        if account.counter != 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be 0 for registration".to_string(),
            ));
        }
        debug_assert_eq!(account.rho.square(), account.current_rho);

        let p_1 = (pk_T_gen * r_1).into_affine();
        let p_2 = (pk_T_gen * r_2).into_affine();
        let T_1 = (pk_T * r_1).into_affine();
        let T_2 = (pk_T * r_2).into_affine();
        let p_1_xy = p_1.xy().unwrap();
        let p_2_xy = p_2.xy().unwrap();
        let x_1 = *p_1_xy.0;
        let y_1 = *p_1_xy.1;
        let x_2 = *p_2_xy.0;
        let y_2 = *p_2_xy.1;

        // x_1 is rho
        // x_2 is randomness
        debug_assert_eq!(account.rho, x_1);
        debug_assert_eq!(account.randomness, x_2);

        let mut transcript = MerlinTranscript::new(REG_TXN_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        account.asset_id.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;
        pk_T.serialize_compressed(&mut extra_instance)?;
        pk_T_gen.serialize_compressed(&mut extra_instance)?;

        let initial_nullifier = account.initial_nullifier(&account_comm_key);

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let r_1_blinding = F1::rand(rng);
        let r_2_blinding = F1::rand(rng);
        let x_1_blinding = F0::rand(rng);
        let x_2_blinding = F0::rand(rng);
        let current_rho_blinding = F0::rand(rng);
        let sk_blinding = F0::rand(rng);
        let comm_bp_blinding = F0::rand(rng);

        // D = pk + g_k * asset_id + g_l * id
        let D = pk.into_group()
            + (account_comm_key.asset_id_gen() * G0::ScalarField::from(account.asset_id))
            + (account_comm_key.id_gen() * account.id);

        // For proving Comm - D - initial_nullifier = g_i * rho^2 + g_j * s
        let comm_protocol = PokPedersenCommitmentProtocol::init(
            account.current_rho,
            current_rho_blinding,
            &account_comm_key.current_rho_gen(),
            account.randomness,
            x_2_blinding,
            &account_comm_key.randomness_gen(),
        );
        let reduced_acc_comm =
            (account_commitment.0.into_group() - D - initial_nullifier.into_group()).into_affine();
        comm_protocol.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;

        // For proving initial_nullifier
        let init_null_protocol =
            PokDiscreteLogProtocol::init(account.rho, x_1_blinding, &account_comm_key.rho_gen());
        init_null_protocol.challenge_contribution(
            &account_comm_key.rho_gen(),
            &initial_nullifier,
            &mut transcript,
        )?;

        let T_1_protocol = PokDiscreteLogProtocol::init(r_1, r_1_blinding, &pk_T);
        T_1_protocol.challenge_contribution(&pk_T, &T_1, &mut transcript)?;
        let T_2_protocol = PokDiscreteLogProtocol::init(r_2, r_2_blinding, &pk_T);
        T_2_protocol.challenge_contribution(&pk_T, &T_2, &mut transcript)?;

        let mut prover = Prover::new(&leaf_level_pc_gens, transcript);
        let (comm_bp, vars) = prover.commit_vec(
            &[x_1, y_1, x_2, y_2, account.current_rho],
            comm_bp_blinding,
            &leaf_level_bp_gens,
        );

        Self::enforce_constraints(&mut prover, Some(r_1), Some(r_2), vars, pk_T_gen_tables)?;

        let mut gens = bp_gens_for_vec_commitment(5, &leaf_level_bp_gens);
        let t_comm_bp = SchnorrCommitment::new(
            &[
                leaf_level_pc_gens.B_blinding,
                gens.next().unwrap(),
                gens.next().unwrap(),
                gens.next().unwrap(),
                gens.next().unwrap(),
                gens.next().unwrap(),
            ],
            vec![
                F0::rand(rng),
                x_1_blinding,
                F0::rand(rng),
                x_2_blinding,
                F0::rand(rng),
                current_rho_blinding,
            ],
        );

        let t_pk =
            PokDiscreteLogProtocol::init(account.sk, sk_blinding, &account_comm_key.sk_gen());

        let mut transcript = prover.transcript();

        t_comm_bp.challenge_contribution(&mut transcript)?;
        t_pk.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript)?;

        let prover_challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let prover_challenge_g1 = transcript.challenge_scalar::<F1>(TXN_CHALLENGE_LABEL);

        let resp_comm = comm_protocol.gen_proof(&prover_challenge);
        let resp_initial_nullifier = init_null_protocol.gen_proof(&prover_challenge);

        let resp_T_1 = T_1_protocol.gen_proof(&prover_challenge_g1);
        let resp_T_2 = T_2_protocol.gen_proof(&prover_challenge_g1);

        let resp_comm_bp = t_comm_bp.response(
            &[comm_bp_blinding, x_1, y_1, x_2, y_2, account.current_rho],
            &prover_challenge,
        )?;
        let resp_pk = t_pk.gen_proof(&prover_challenge);

        let proof = prover.prove_with_rng(leaf_level_bp_gens, rng)?;

        Ok(Self {
            T_1,
            T_2,
            resp_comm,
            resp_initial_nullifier,
            comm_bp,
            t_comm_bp: t_comm_bp.t,
            resp_comm_bp,
            resp_pk,
            initial_nullifier,
            resp_T_1,
            resp_T_2,
            proof,
        })
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        id: G0::ScalarField,
        pk: &Affine<G0>,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<Affine<G0>>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        pk_T: Affine<G1>,
        pk_T_gen: Affine<G1>,
        pk_T_gen_tables: &[Lookup3Bit<2, F0>],
        leaf_level_pc_gens: &PedersenGens<Affine<G0>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G0>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(REG_TXN_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        asset_id.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;
        pk_T.serialize_compressed(&mut extra_instance)?;
        pk_T_gen.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // D = pk + g_k * asset_id + g_l * id
        let D = pk.into_group()
            + (account_comm_key.asset_id_gen() * F0::from(asset_id))
            + (account_comm_key.id_gen() * id);

        let reduced_acc_comm =
            (account_commitment.0.into_group() - D - self.initial_nullifier.into_group())
                .into_affine();
        self.resp_comm.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;

        self.resp_initial_nullifier.challenge_contribution(
            &account_comm_key.rho_gen(),
            &self.initial_nullifier,
            &mut transcript,
        )?;

        self.resp_T_1
            .challenge_contribution(&pk_T, &self.T_1, &mut transcript)?;
        self.resp_T_2
            .challenge_contribution(&pk_T, &self.T_2, &mut transcript)?;

        let mut verifier = Verifier::new(transcript);

        let vars = verifier.commit_vec(5, self.comm_bp);
        Self::enforce_constraints(&mut verifier, None, None, vars, pk_T_gen_tables)?;

        let mut transcript = verifier.transcript();

        self.t_comm_bp.serialize_compressed(&mut transcript)?;
        self.resp_pk
            .challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript)?;

        let verifier_challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let verifier_challenge_g1 = transcript.challenge_scalar::<F1>(TXN_CHALLENGE_LABEL);

        if !self.resp_comm.verify(
            &reduced_acc_comm,
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Account commitment verification failed".to_string(),
            ));
        }

        if !self.resp_initial_nullifier.verify(
            &self.initial_nullifier,
            &account_comm_key.rho_gen(),
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Initial nullifier verification failed".to_string(),
            ));
        }

        let mut gens = bp_gens_for_vec_commitment(5, &leaf_level_bp_gens);

        self.resp_comm_bp.is_valid(
            &[
                leaf_level_pc_gens.B_blinding,
                gens.next().unwrap(),
                gens.next().unwrap(),
                gens.next().unwrap(),
                gens.next().unwrap(),
                gens.next().unwrap(),
            ],
            &self.comm_bp,
            &self.t_comm_bp,
            &verifier_challenge,
        )?;

        if !self
            .resp_pk
            .verify(pk, &account_comm_key.sk_gen(), &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "Public key verification failed".to_string(),
            ));
        }

        if !self
            .resp_T_1
            .verify(&self.T_1, &pk_T, &verifier_challenge_g1)
        {
            return Err(Error::ProofVerificationError(
                "T_1 verification failed".to_string(),
            ));
        }

        if !self
            .resp_T_2
            .verify(&self.T_2, &pk_T, &verifier_challenge_g1)
        {
            return Err(Error::ProofVerificationError(
                "T_2 verification failed".to_string(),
            ));
        }

        // Question: How do i make responses for r_1 and r_2 consistent or it isn't needed?
        // If needed, should i allocate variables but that will be in a different R1CS proof so the cost increases.
        // Maybe i replace sigma protocol of T_1 and T_2 with a BP proof but that means 2 more scalar mult

        if self.resp_comm_bp.0[1] != self.resp_initial_nullifier.response {
            return Err(Error::ProofVerificationError(
                "Initial rho mismatch between BP commitment and initial nullifier".to_string(),
            ));
        }
        if self.resp_comm_bp.0[3] != self.resp_comm.response2 {
            return Err(Error::ProofVerificationError(
                "Randomness mismatch between account and BP commitment".to_string(),
            ));
        }
        if self.resp_comm_bp.0[5] != self.resp_comm.response1 {
            return Err(Error::ProofVerificationError(
                "Rho mismatch between account and BP commitment".to_string(),
            ));
        }

        verifier.verify_with_rng(&self.proof, leaf_level_pc_gens, &leaf_level_bp_gens, rng)?;

        Ok(())
    }

    fn enforce_constraints<CS: ConstraintSystem<F0>>(
        cs: &mut CS,
        r_1: Option<F1>,
        r_2: Option<F1>,
        mut vars: Vec<Variable<F0>>,
        tables: &[Lookup3Bit<2, F0>],
    ) -> Result<()> {
        let var_x_1 = vars.remove(0);
        let var_y_1 = vars.remove(0);
        let var_x_2 = vars.remove(0);
        let var_y_2 = vars.remove(0);
        let var_rho_sq = vars.remove(0);

        let (_, lc_x_1, lc_y_1) = scalar_mult::<F0, F1, G1, _>(cs, &tables, r_1)?;
        let (_, lc_x_2, lc_y_2) = scalar_mult::<F0, F1, G1, _>(cs, &tables, r_2)?;

        curve_check(cs, lc_x_1.clone(), lc_y_1.clone(), G1::COEFF_A, G1::COEFF_B);

        curve_check(cs, lc_x_2.clone(), lc_y_2.clone(), G1::COEFF_A, G1::COEFF_B);

        let (_, _, var_rho_sq_1) = cs.multiply(lc_x_1.clone(), lc_x_1.clone());
        cs.constrain(lc_x_1 - var_x_1);
        cs.constrain(lc_y_1 - var_y_1);
        cs.constrain(lc_x_2 - var_x_2);
        cs.constrain(lc_y_2 - var_y_2);
        cs.constrain(var_rho_sq_1 - var_rho_sq);
        Ok(())
    }
}

/// Decomposes a field element into base 2^BASE_BITS with NUM_DIGITS digits in total.
pub fn digits<F: PrimeField, const BASE_BITS: usize, const NUM_DIGITS: usize>(
    scalar: F,
) -> ([F; NUM_DIGITS], [u64; NUM_DIGITS]) {
    let mut chunks = [F::zero(); NUM_DIGITS];
    let mut chunks_as_u64 = [0; NUM_DIGITS];
    let bits = scalar.into_bigint().to_bits_le();
    let mut bit_idx = 0;
    for chunk_i in 0..NUM_DIGITS {
        let mut val = 0u64;
        for bit_i in 0..BASE_BITS {
            if bit_idx < bits.len() && bits[bit_idx] {
                val |= 1 << bit_i;
            }
            bit_idx += 1;
        }
        chunks_as_u64[chunk_i] = val;
        chunks[chunk_i] = F::from(val);
    }
    (chunks, chunks_as_u64)
}

/// Returns powers of 2 as field elements for use with digits decomposition.
pub fn powers_of_base<F: PrimeField, const BASE_BITS: usize, const NUM_DIGITS: usize>()
-> [F; NUM_DIGITS] {
    let mut powers = [F::zero(); NUM_DIGITS];
    let base = F::from(1u64 << BASE_BITS);
    for i in 0..NUM_DIGITS {
        if i == 0 {
            powers[i] = F::one();
        } else {
            powers[i] = powers[i - 1] * base;
        }
    }
    powers
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account::NUM_GENERATORS;
    use crate::keys::{SigKey, keygen_enc, keygen_sig};
    use crate::poseidon_impls::poseidon_2::Poseidon_hash_2_simple;
    use crate::poseidon_impls::poseidon_2::Poseidon2Params;
    use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
    use ark_crypto_primitives::crh::{TwoToOneCRHScheme, TwoToOneCRHSchemeGadget};
    use ark_crypto_primitives::{
        crh::poseidon::{TwoToOneCRH, constraints::TwoToOneCRHGadget},
        sponge::poseidon::PoseidonConfig,
    };
    use ark_ff::{Field, PrimeField};
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::{
        R1CSVar,
        fields::fp::{AllocatedFp, FpVar},
    };
    use ark_std::UniformRand;
    use curve_tree_relations::curve_tree::SelRerandParameters;
    use curve_tree_relations::rerandomize::build_tables;
    use polymesh_dart_common::AssetId;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type VestaA = ark_vesta::Affine;
    type Fr = ark_pallas::Fr;

    pub fn test_params_for_poseidon_0<R: CryptoRngCore, F: PrimeField>(
        rng: &mut R,
    ) -> PoseidonConfig<F> {
        // Parameters for testing only.
        const RATE: usize = 2;
        const CAPACITY: usize = 1;
        const WIDTH: usize = RATE + CAPACITY;
        const FULL_ROUNDS: usize = 8;
        const PARTIAL_ROUNDS: usize = 10;
        const ALPHA: u64 = 3;

        let mut mds = vec![vec![]; WIDTH];
        for i in 0..WIDTH {
            for _ in 0..WIDTH {
                mds[i].push(F::rand(rng));
            }
        }

        let mut ark = vec![vec![]; FULL_ROUNDS + PARTIAL_ROUNDS];
        for i in 0..FULL_ROUNDS + PARTIAL_ROUNDS {
            for _ in 0..WIDTH {
                ark[i].push(F::rand(rng));
            }
        }

        PoseidonConfig::<F>::new(FULL_ROUNDS, PARTIAL_ROUNDS, ALPHA, mds, ark, RATE, CAPACITY)
    }

    pub fn test_params_for_poseidon2<R: CryptoRngCore, F: PrimeField>(
        rng: &mut R,
    ) -> Poseidon2Params<F> {
        // NOTE: These numbers are for 2:1 compression and 256 bit group (Table 1 from Poseidon2 paper) and that is the only config we use. These should be changed if we decide to use something else.
        let full_rounds = 8;
        let partial_rounds = 56;
        let degree = 5;
        Poseidon2Params::new_with_randoms(rng, 3, degree, full_rounds, partial_rounds).unwrap()
    }

    #[test]
    fn test_poseidon() {
        let mut rng = rand::thread_rng();

        let params = test_params_for_poseidon_0::<_, Fr>(&mut rng);

        let a = Fr::rand(&mut rng);
        let b = Fr::rand(&mut rng);
        let c = TwoToOneCRH::<Fr>::compress(&params, a.clone(), b.clone()).unwrap();

        use ark_relations::r1cs::ConstraintSystem as CS;
        let cs = CS::<Fr>::new_ref();

        let a_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(a)).unwrap());
        let b_var = FpVar::Var(AllocatedFp::<Fr>::new_witness(cs.clone(), || Ok(b)).unwrap());

        let params_g = CRHParametersVar::<Fr>::new_witness(cs.clone(), || Ok(params)).unwrap();

        let c_var = TwoToOneCRHGadget::<Fr>::compress(&params_g, &a_var, &b_var).unwrap();

        assert_eq!(a, a_var.value().unwrap());
        assert_eq!(b, b_var.value().unwrap());
        assert_eq!(c, c_var.value().unwrap());

        // cs.finalize();
        // Can't get constraints as its private. Work with matrices.
        // let mats = cs.to_matrices().unwrap();
        // let cs_inner = cs.into_inner();
        // println!("{}", cs_inner.is_some());
        // TODO:
    }

    // TODO: Modify to create all generators by hashing public strings
    pub fn setup_comm_key<R: CryptoRngCore, G: AffineRepr>(
        rng: &mut R,
    ) -> impl AccountCommitmentKeyTrait<G> + use<R, G> {
        let account_comm_key: [G; NUM_GENERATORS] = (0..NUM_GENERATORS)
            .map(|_| G::rand(rng))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        account_comm_key
    }

    // pub fn new_account<R: CryptoRngCore, G: AffineRepr>(rng: &mut R, asset_id: AssetId, sk: SigKey<G>) -> (AccountState<G>, NullifierSkGenCounter, PoseidonConfig<G::ScalarField>) where G::ScalarField: Absorb {
    pub fn new_account<R: CryptoRngCore, G: AffineRepr>(
        rng: &mut R,
        asset_id: AssetId,
        sk: SigKey<G>,
        id: G::ScalarField,
    ) -> (
        AccountState<G>,
        NullifierSkGenCounter,
        Poseidon2Params<G::ScalarField>,
    ) {
        let params = test_params_for_poseidon2::<_, G::ScalarField>(rng);
        let counter = 1;
        let account = AccountState::new(rng, id, sk.0, asset_id, counter, params.clone()).unwrap();
        (account, counter, params)
    }

    #[test]
    fn account_init() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

        let asset_id = 1;

        // Issuer creates keys
        let (sk_i, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        // User hashes it id onto the field
        let id = Fr::rand(&mut rng);

        let (account, c, poseidon_config) = new_account::<_, PallasA>(&mut rng, asset_id, sk_i, id);
        assert_eq!(account.id, id);
        assert_eq!(account.asset_id, asset_id);
        assert_eq!(account.balance, 0);
        assert_eq!(account.counter, 0);
        let combined = AccountState::<PallasA>::concat_asset_id_counter(asset_id, c);
        let expected_rho =
            Poseidon_hash_2_simple::<Fr>(account.sk, combined, poseidon_config).unwrap();
        assert_eq!(account.rho, expected_rho);
        assert_eq!(account.current_rho, account.rho.square());

        account.commit(account_comm_key).unwrap();
    }

    #[test]
    fn registration_without_pk_T() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS)
                .unwrap();

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

        let asset_id = 1;

        // Investor creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);

        let clock = Instant::now();
        let (account, nullifier_gen_counter, poseidon_params) =
            new_account::<_, PallasA>(&mut rng, asset_id, sk_i, id.clone());
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce-0";

        let reg_proof = RegTxnProof::<_, 48, 6>::new(
            &mut rng,
            pk_i.0,
            &account,
            account_comm.clone(),
            nullifier_gen_counter,
            nonce,
            account_comm_key.clone(),
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            &poseidon_params,
            None,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        reg_proof
            .verify(
                &mut rng,
                id,
                &pk_i.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key,
                &account_tree_params.even_parameters.pc_gens,
                &account_tree_params.even_parameters.bp_gens,
                &poseidon_params,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("For reg. txn");
        log::info!("total proof size = {}", reg_proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn registration_with_pk_T() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

        const CHUNK_BITS: usize = 48;
        const NUM_CHUNKS: usize = 6;

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS)
                .unwrap();

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

        let asset_id = 1;

        // Investor creates keys
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);

        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);
        let (sk_T, pk_T) = keygen_enc(&mut rng, enc_key_gen);

        let clock = Instant::now();
        let (mut account, nullifier_gen_counter, poseidon_params) =
            new_account::<_, PallasA>(&mut rng, asset_id, sk, id.clone());
        // Make randomness small to run test faster
        account.randomness = Fr::from(u16::rand(&mut rng) as u64 + u8::rand(&mut rng) as u64);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce-0";

        let reg_proof = RegTxnProof::<_, 48, 6>::new(
            &mut rng,
            pk.0,
            &account,
            account_comm.clone(),
            nullifier_gen_counter,
            nonce,
            account_comm_key.clone(),
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            &poseidon_params,
            Some((pk_T.0, enc_key_gen, enc_gen)),
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        reg_proof
            .verify(
                &mut rng,
                id,
                &pk.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key,
                &account_tree_params.even_parameters.pc_gens,
                &account_tree_params.even_parameters.bp_gens,
                &poseidon_params,
                Some((pk_T.0, enc_key_gen, enc_gen)),
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For reg. txn with {NUM_CHUNKS} chunks each of {CHUNK_BITS} bits");
        println!("total proof size = {}", reg_proof.compressed_size());
        println!(
            "ciphertext and its proof size = {}",
            reg_proof
                .encrypted_randomness
                .as_ref()
                .unwrap()
                .compressed_size()
        );
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );

        // This will take a long time to decrypt
        let clock = Instant::now();
        assert_eq!(
            account.randomness,
            reg_proof
                .encrypted_randomness
                .unwrap()
                .decrypt(&sk_T.0, enc_gen.into_group())
                .unwrap()
        );
        println!("decryption time = {:?}", clock.elapsed());
    }

    #[test]
    fn registration_alt() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS)
                .unwrap();

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

        let asset_id = 1;

        // Investor creates keys
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);

        let enc_key_gen = VestaA::rand(&mut rng);
        let (sk_T, pk_T) = keygen_enc(&mut rng, enc_key_gen);
        let tables = build_tables(enc_key_gen).unwrap();

        let clock = Instant::now();
        let (account, r_1, r_2) =
            AccountState::new_alt(&mut rng, id.clone(), sk.0, asset_id, enc_key_gen).unwrap();
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce-0";

        let reg_proof = RegTxnProofAlt::new(
            &mut rng,
            pk.0,
            &account,
            account_comm.clone(),
            r_1,
            r_2,
            nonce,
            account_comm_key.clone(),
            pk_T.0,
            enc_key_gen,
            &tables,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        reg_proof
            .verify(
                &mut rng,
                id,
                &pk.0,
                asset_id,
                &account_comm,
                nonce,
                account_comm_key,
                pk_T.0,
                enc_key_gen,
                &tables,
                &account_tree_params.even_parameters.pc_gens,
                &account_tree_params.even_parameters.bp_gens,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For reg. txn");
        println!("total proof size = {}", reg_proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );

        let sk_inv = sk_T.0.inverse().unwrap();
        assert_eq!(
            *(reg_proof.T_1 * sk_inv).into_affine().x().unwrap(),
            account.rho
        );
        assert_eq!(
            *(reg_proof.T_2 * sk_inv).into_affine().x().unwrap(),
            account.randomness
        );
    }

    #[test]
    fn test_digits() {
        let mut rng = rand::thread_rng();

        const CHUNK_BITS: usize = 8;
        const NUM_CHUNKS: usize = 4;
        let val = Fr::from(0xAABBCCDDu64);
        let (d, _) = digits::<Fr, CHUNK_BITS, NUM_CHUNKS>(val);
        // 0xAABBCCDD = [0xDD, 0xCC, 0xBB, 0xAA] in little-endian
        assert_eq!(d[0], Fr::from(0xDDu64));
        assert_eq!(d[1], Fr::from(0xCCu64));
        assert_eq!(d[2], Fr::from(0xBBu64));
        assert_eq!(d[3], Fr::from(0xAAu64));

        let powers = powers_of_base::<Fr, CHUNK_BITS, NUM_CHUNKS>();
        let mut reconstructed = Fr::zero();
        for i in 0..NUM_CHUNKS {
            reconstructed += d[i] * powers[i];
        }
        assert_eq!(reconstructed, val);

        const B: usize = 48;
        const N: usize = 6;
        let powers = powers_of_base::<Fr, B, N>();
        for _ in 0..100 {
            let val = Fr::rand(&mut rng);
            let (d, u) = digits::<Fr, B, N>(val);
            let mut reconstructed = Fr::zero();
            for i in 0..N {
                reconstructed += d[i] * powers[i];
                assert_eq!(d[i], Fr::from(u[i]))
            }
            assert_eq!(reconstructed, val);
        }
    }

    fn prove_verify_rho_gen_constraints(
        pc_gens: &PedersenGens<PallasA>,
        bp_gens: &BulletproofGens<PallasA>,
        sk: Fr,
        rho: Fr,
        current_rho: Fr,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        poseidon_params: &Poseidon2Params<Fr>,
    ) -> bool {
        let values = vec![sk, rho, current_rho];

        let prover_transcript = MerlinTranscript::new(b"test");
        let mut prover = Prover::new(pc_gens, prover_transcript);
        let (comm, vars) = prover.commit_vec(&values, Fr::from(200u64), bp_gens);

        if RegTxnProof::<PallasA, 48, 6>::enforce_constraints(
            &mut prover,
            asset_id,
            counter,
            vars,
            &poseidon_params,
        )
        .is_err()
        {
            return false;
        }

        let proof = match prover.prove(bp_gens) {
            Ok(p) => p,
            Err(_) => return false,
        };

        let verifier_transcript = MerlinTranscript::new(b"test");
        let mut verifier = Verifier::new(verifier_transcript);
        let vars = verifier.commit_vec(3, comm);

        if RegTxnProof::<PallasA, 48, 6>::enforce_constraints(
            &mut verifier,
            asset_id,
            counter,
            vars,
            &poseidon_params,
        )
        .is_err()
        {
            return false;
        }

        verifier.verify(&proof, pc_gens, bp_gens).is_ok()
    }

    #[test]
    fn test_rho_gen_constraints() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(256, 1);
        let mut rng = rand::thread_rng();

        let sk = Fr::rand(&mut rng);
        let asset_id = 2;
        let counter = 1;

        let poseidon_params = test_params_for_poseidon2::<_, Fr>(&mut rng);
        let combined = AccountState::<PallasA>::concat_asset_id_counter(asset_id, counter);
        let rho = Poseidon_hash_2_simple::<Fr>(sk, combined, poseidon_params.clone()).unwrap();
        let current_rho = rho.square();

        assert!(prove_verify_rho_gen_constraints(
            &pc_gens,
            &bp_gens,
            sk,
            rho,
            current_rho,
            asset_id,
            counter,
            &poseidon_params
        ));

        let wrong_rho = Fr::rand(&mut rng);
        assert!(!prove_verify_rho_gen_constraints(
            &pc_gens,
            &bp_gens,
            sk,
            wrong_rho,
            current_rho,
            asset_id,
            counter,
            &poseidon_params
        ));

        let wrong_current_rho = Fr::rand(&mut rng);
        assert!(!prove_verify_rho_gen_constraints(
            &pc_gens,
            &bp_gens,
            sk,
            rho,
            wrong_current_rho,
            asset_id,
            counter,
            &poseidon_params
        ));
    }
}
