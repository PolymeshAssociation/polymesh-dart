use crate::types_and_constants::{TXN_CHALLENGE_LABEL, TXN_INSTANCE_LABEL};
use crate::utils::TranscriptWriter;
use crate::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, AffineSerializable,
    error::{Error, Result},
};
use ff::{Field, PrimeField, PrimeFieldBits};
use group::{Curve, Group};
use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
use halo2_poseidon::{P128Pow5T3, Spec};
use halo2_proofs::circuit::Value;
use halo2_proofs::dev::MockProver;
use halo2_proofs::plonk::{create_proof_with_given_column_blindings, get_advice_and_precommitted_col_comms, get_the_only_precommitted_col_comm, verify_proof, ProvingKey, SingleVerifier, VerifyingKey};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use merlin::Transcript;
use multiexp::multiexp_vartime;
use polymesh_dart_common::{AssetId, NullifierSkGenCounter};
use rand_core::CryptoRngCore;
use sigma_protocols::{CommitmentToRandomness, Response, SigmaChallengeContributor};
use sigma_protocols::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use zkcrypto_utils::elgamal::Ciphertext;
use zkcrypto_utils::ff_utils::inner_product;
use zkcrypto_utils::solve_discrete_log::solve_discrete_log_bsgs_alt;
use crate::circuits::registration::{AccountRegCircuit, AccountRegWithEncCircuit, PRECOMMITTED_CHUNKS_START_IDX, PRECOMMITTED_RHO_IDX, PRECOMMITTED_RHO_SQ_IDX, PRECOMMITTED_SK_IDX};

// TODO: Remove hardcoding
const LIMB_BITS: usize = 6;
const NUM_WORDS: usize = 8;

/// Proof of encrypted randomness
// TODO: Check if i can use Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf).
// The problem is that response of all chunks is aggregated in one value so tying it with BP is not straightforward. So need to check if aggregating
// those responses and comparing is safe
#[derive(Clone, Debug)]
pub struct EncryptedRandomness<
    G: AffineSerializable,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    pub ciphertexts: [Ciphertext<G>; NUM_CHUNKS],
    /// For relation `g * r_i`
    pub resp_eph_pk: [PokDiscreteLog<G>; NUM_CHUNKS],
    /// For relation `pk_T * r_i + h * s_i`
    pub resp_encrypted: [PokPedersenCommitment<G>; NUM_CHUNKS],
    /// For Pedersen commitment to the weighted randomness and chunks. The weighted chunks equals the account commitment randomness
    pub resp_combined_s: PokPedersenCommitment<G>,
}

/// This is the proof for user registering its (signing) public key for an asset. Report section 5.1.3, called "Account Registration"
/// We could register both signing and encryption keys by modifying this proof even though the encryption isn't used in account commitment.
#[derive(Clone, Debug)]
pub struct RegTxnProof<
    G: AffineSerializable,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    pub resp_acc_comm: PokPedersenCommitment<G>,
    pub resp_initial_nullifier: PokDiscreteLog<G>,
    /// Called `N` in the report. This helps during account freezing to remove `g_i * rho` term from account state commitment.
    pub initial_nullifier: G,
    pub resp_pk: PokDiscreteLog<G>,
    /// Called `uppercase Omega` in the report
    pub encrypted_randomness: Option<EncryptedRandomness<G, CHUNK_BITS, NUM_CHUNKS>>,
    pub comm_sk_rho_halo2: G,
    pub resp_comm_sk_rho_halo2: Response<G>,
    pub snark_proof: Vec<u8>,
}

const REG_TXN_LABEL: &'static [u8; 12] = b"registration";

impl<G: AffineSerializable, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnProof<G, CHUNK_BITS, NUM_CHUNKS> where
    P128Pow5T3: Spec<G::Scalar, 3, 2>,
{
    // ceil(MODULUS_BIT_SIZE/CHUNK_BITS) == NUM_CHUNKS
    const CHECK_CHUNK_BITS: () = assert!(
        CHUNK_BITS <= 48
            && ((<G::ScalarExt as PrimeField>::NUM_BITS as usize + CHUNK_BITS - 1) / CHUNK_BITS
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
        params: &Params<G>,
        proving_key: &ProvingKey<G>,
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

        let mut transcript = Transcript::new(REG_TXN_LABEL);

        let mut transcript_writer = TranscriptWriter(&mut transcript);

        let mut extra_instance = Vec::new();
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(account.asset_id.to_le_bytes().as_ref());
        extra_instance.extend_from_slice(account_commitment.0.to_bytes().as_ref());
        extra_instance.extend_from_slice(pk.to_bytes().as_ref());

        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let initial_nullifier = account.initial_nullifier(&account_comm_key);

        // D = pk + g_k * asset_id
        let D = pk.to_curve()
            + (account_comm_key.asset_id_gen() * G::ScalarExt::from(account.asset_id.into()));

        let sk_blinding = G::ScalarExt::random(&mut *rng);
        let rho_blinding = G::ScalarExt::random(&mut *rng);
        let current_rho_blinding = G::ScalarExt::random(&mut *rng);
        let s_blinding = G::ScalarExt::random(&mut *rng);

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
            (account_commitment.0.to_curve() - D - initial_nullifier.to_curve()).to_affine();
        comm_protocol.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript_writer,
        )?;

        // For proving initial_nullifier
        let init_null_protocol =
            PokDiscreteLogProtocol::init(account.rho, rho_blinding, &account_comm_key.rho_gen());
        init_null_protocol.challenge_contribution(
            &account_comm_key.rho_gen(),
            &initial_nullifier,
            &mut transcript_writer,
        )?;

        // TODO: Try combining all these into 1 eq by RLC. Bases need to be adapted accordingly so it might not lead to that performant solution
        // Break randomness `s` in `NUM_CHUNKS` chunks and encrypt each chunk using exponent Elgamal. Then initialize sigma
        // protocols for proving correctness of each ciphertext
        let enc_prep = if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            let (s_chunks, s_chunks_as_u64) =
                digits::<G::ScalarExt, CHUNK_BITS, NUM_CHUNKS>(account.randomness);

            // encs[i] = h * s_chunks[i]
            let mut encs = vec![G::identity(); NUM_CHUNKS];
            // Note: batch_normalize might not be available, using individual normalization
            for (i, chunk) in s_chunks.iter().enumerate() {
                encs[i] = (enc_gen.to_curve() * chunk).to_affine();
            }

            let enc_rands = (0..NUM_CHUNKS)
                .map(|_| G::ScalarExt::random(&mut *rng))
                .collect::<Vec<_>>();

            let s_chunks_blindings = (0..NUM_CHUNKS)
                .map(|_| G::ScalarExt::random(&mut *rng))
                .collect::<Vec<_>>();
            let enc_rands_blindings = (0..NUM_CHUNKS)
                .map(|_| G::ScalarExt::random(&mut *rng))
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
                    &mut transcript_writer,
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
                    &mut transcript_writer,
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

        let t_pk =
            PokDiscreteLogProtocol::init(account.sk, sk_blinding, &account_comm_key.sk_gen());

        t_pk.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript_writer)?;

        let num_blindings_halo2 = proving_key.get_vk().blinding_factors() + 2;
        let mut blinding_rows_halo2 = (0..num_blindings_halo2)
            .map(|_| G::Scalar::random(&mut *rng))
            .collect::<Vec<_>>();
        let usable_rows = params.n as usize - (num_blindings_halo2 - 1);
        let mut halo2_transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        // TODO: Write hash of merlin transcript into halo2_transcript using common_point

        let combined = AccountState::<G>::concat_asset_id_counter(account.asset_id, counter);

        let mut bases_halo2 = Vec::with_capacity(3 + NUM_CHUNKS + num_blindings_halo2);
        let mut witnesses_halo2 = Vec::with_capacity(3 + NUM_CHUNKS + num_blindings_halo2);
        let mut blindings_halo2 = Vec::with_capacity(3 + NUM_CHUNKS + num_blindings_halo2);

        bases_halo2.push(params.g_lagrange[PRECOMMITTED_SK_IDX]);
        bases_halo2.push(params.g_lagrange[PRECOMMITTED_RHO_IDX]);
        bases_halo2.push(params.g_lagrange[PRECOMMITTED_RHO_SQ_IDX]);
        witnesses_halo2.push(account.sk);
        witnesses_halo2.push(account.rho);
        witnesses_halo2.push(account.current_rho);
        blindings_halo2.push(sk_blinding);
        blindings_halo2.push(rho_blinding);
        blindings_halo2.push(current_rho_blinding);

        if let Some((s_chunks, _, _, _, s_chunks_blindings, _, _)) = &enc_prep {
            let mut chunks = [Value::unknown(); NUM_CHUNKS];
            for i in 0..NUM_CHUNKS {
                chunks[i] = Value::known(s_chunks[i]);
                bases_halo2.push(params.g_lagrange[PRECOMMITTED_CHUNKS_START_IDX+i]);
                witnesses_halo2.push(s_chunks[i]);
                blindings_halo2.push(s_chunks_blindings[i]);
            }

            let circuit = AccountRegWithEncCircuit::<
                G::Scalar,
                LookupRangeCheckConfig<G::Scalar, LIMB_BITS>,
                NUM_CHUNKS,
                LIMB_BITS,
            >::new(NUM_WORDS, Value::known(account.sk), Value::known(account.rho), Value::known(account.current_rho), chunks);

            if cfg!(debug_assertions) {
                let prover = MockProver::run(params.k, &circuit, vec![vec![combined]]).unwrap();
                prover.assert_satisfied();
            }

            create_proof_with_given_column_blindings(
                params,
                proving_key,
                &[circuit],
                &[&[&[combined]]],
                vec![Some(vec![blinding_rows_halo2.clone()])],
                &mut *rng,
                &mut halo2_transcript,
            )
                .unwrap();
        } else {
            let circuit = AccountRegCircuit::<G::Scalar>::new(Value::known(account.sk), Value::known(account.rho), Value::known(account.current_rho));

            if cfg!(debug_assertions) {
                let prover = MockProver::run(params.k, &circuit, vec![vec![combined]]).unwrap();
                prover.assert_satisfied();
            }

            create_proof_with_given_column_blindings(
                params,
                proving_key,
                &[circuit],
                &[&[&[combined]]],
                vec![Some(vec![blinding_rows_halo2.clone()])],
                &mut *rng,
                &mut halo2_transcript,
            )
                .unwrap();
        }

        let snark_proof = halo2_transcript.finalize();
        let mut t = Blake2bRead::<_, _, Challenge255<_>>::init(snark_proof.as_slice());
        let comm_sk_rho_h2 = get_the_only_precommitted_col_comm(proving_key.get_vk(), &mut t).unwrap();

        for i in 0..(num_blindings_halo2 -1) {
            bases_halo2.push(params.g_lagrange[usable_rows+i]);
            witnesses_halo2.push(blinding_rows_halo2.remove(0));
            blindings_halo2.push(G::Scalar::random(&mut *rng));
        }

        bases_halo2.push(params.w);
        witnesses_halo2.push(blinding_rows_halo2.remove(0));
        blindings_halo2.push(G::Scalar::random(&mut *rng));

        debug_assert_eq!(blinding_rows_halo2.len(), 0);

        let t_comm_sk_rho_halo2 = CommitmentToRandomness::new(&bases_halo2, blindings_halo2);
        t_comm_sk_rho_halo2.challenge_contribution(&mut transcript_writer)?;

        // Take challenge contribution of ciphertext of each chunk
        // TODO:
        // let (t_comm_s_chunks_bp, combined_s_proto) =
        let combined_s_proto =
            if let Some((_, _, enc_rands, _, _, _, _)) = &enc_prep {
                let powers = powers_of_base::<G::ScalarExt, CHUNK_BITS, NUM_CHUNKS>();
                let combined_enc_rand = inner_product::<G::ScalarExt>(enc_rands, &powers);
                let pk_T = T.as_ref().unwrap().0;
                let h = T.as_ref().unwrap().2;
                let combined_s_commitment = (pk_T.to_curve() * combined_enc_rand
                    + h.to_curve() * account.randomness)
                    .to_affine();

                let combined_s_proto = PokPedersenCommitmentProtocol::init(
                    combined_enc_rand,
                    G::ScalarExt::random(&mut *rng),
                    &pk_T,
                    account.randomness,
                    s_blinding,
                    &h,
                );
                combined_s_proto.challenge_contribution(
                    &pk_T,
                    &h,
                    &combined_s_commitment,
                    &mut transcript_writer,
                )?;

                Some(combined_s_proto)
            } else {
                None
            };

        let prover_challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);
        println!("prover_challenge {:?}", prover_challenge);

        let resp_comm = comm_protocol.gen_proof(&prover_challenge);
        let resp_initial_nullifier = init_null_protocol.gen_proof(&prover_challenge);

        let resp_pk = t_pk.gen_proof(&prover_challenge);

        let resp_comm_sk_rho_h2 = t_comm_sk_rho_halo2.response(&witnesses_halo2, &prover_challenge)?;

        let encrypted_randomness =
            if let Some((_, _, _, ciphertexts, _, eph_proto, enc_proto)) = enc_prep {
                let mut resp_eph_pk = Vec::with_capacity(NUM_CHUNKS);
                let mut resp_encrypted = Vec::with_capacity(NUM_CHUNKS);

                // Generate responses for each protocol
                for proto in eph_proto {
                    resp_eph_pk.push(proto.gen_proof(&prover_challenge));
                }
                for proto in enc_proto {
                    resp_encrypted.push(proto.gen_proof(&prover_challenge));
                }

                let resp_combined_s = combined_s_proto.unwrap().gen_proof(&prover_challenge);

                Some(EncryptedRandomness::<G, CHUNK_BITS, NUM_CHUNKS> {
                    ciphertexts: ciphertexts.try_into().unwrap(),
                    resp_eph_pk: resp_eph_pk.try_into().unwrap(),
                    resp_encrypted: resp_encrypted.try_into().unwrap(),
                    resp_combined_s,
                })
            } else {
                None
            };

        Ok(Self {
            resp_acc_comm: resp_comm,
            resp_initial_nullifier,
            resp_pk,
            initial_nullifier,
            encrypted_randomness,
            comm_sk_rho_halo2: comm_sk_rho_h2,
            resp_comm_sk_rho_halo2: resp_comm_sk_rho_h2,
            snark_proof
        })
    }

    pub fn verify(
        &self,
        pk: &G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        params: &Params<G>,
        verifying_key: &VerifyingKey<G>,
        T: Option<(G, G, G)>,
    ) -> Result<()> {
        let _ = Self::CHECK_CHUNK_BITS;
        if T.is_none() ^ self.encrypted_randomness.is_none() {
            return Err(Error::PkTAndEncryptedRandomnessInconsistent);
        }
        let num_blindings_halo2 = verifying_key.blinding_factors() + 2;
        let usable_rows = params.n as usize - (num_blindings_halo2 - 1);
        if T.is_some() {
            if self.resp_comm_sk_rho_halo2.len() != (3 + NUM_CHUNKS + num_blindings_halo2) {
                return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(3 + NUM_CHUNKS + num_blindings_halo2, self.resp_comm_sk_rho_halo2.len()))
            }
        } else {
            if self.resp_comm_sk_rho_halo2.len() != (3 + num_blindings_halo2) {
                return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(3 + num_blindings_halo2, self.resp_comm_sk_rho_halo2.len()))
            }
        }

        let mut transcript = Transcript::new(REG_TXN_LABEL);

        let mut transcript_writer = TranscriptWriter(&mut transcript);

        let mut extra_instance = Vec::new();
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(asset_id.to_le_bytes().as_ref());
        extra_instance.extend_from_slice(account_commitment.0.to_bytes().as_ref());
        extra_instance.extend_from_slice(pk.to_bytes().as_ref());

        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        // D = pk + g_k * asset_id
        let D =
            pk.to_curve() + (account_comm_key.asset_id_gen() * G::ScalarExt::from(asset_id as u64));

        let reduced_acc_comm =
            (account_commitment.0.to_curve() - D - self.initial_nullifier.to_curve()).to_affine();
        self.resp_acc_comm.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript_writer,
        )?;

        self.resp_initial_nullifier.challenge_contribution(
            &account_comm_key.rho_gen(),
            &self.initial_nullifier,
            &mut transcript_writer,
        )?;

        // Take challenge contribution of ciphertext of each chunk
        if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            let enc_rand = self.encrypted_randomness.as_ref().unwrap();
            for i in 0..NUM_CHUNKS {
                enc_rand.resp_eph_pk[i].challenge_contribution(
                    enc_key_gen,
                    &enc_rand.ciphertexts[i].eph_pk,
                    &mut transcript_writer,
                )?;
                enc_rand.resp_encrypted[i].challenge_contribution(
                    pk_T,
                    enc_gen,
                    &enc_rand.ciphertexts[i].encrypted,
                    &mut transcript_writer,
                )?;
            }
        }

        self.resp_pk.challenge_contribution(
            &account_comm_key.sk_gen(),
            &pk,
            &mut transcript_writer,
        )?;

        let combined = AccountState::<G>::concat_asset_id_counter(asset_id, counter);

        let strategy = SingleVerifier::new(params);
        let mut halo2_transcript = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof.as_slice());

        // TODO: Read hash of merlin transcript from halo2_transcript using common_point and check equality. Is there a better way?
        verify_proof(params, verifying_key, strategy, &[&[&[combined]]], &mut halo2_transcript).unwrap();

        // TODO: Can't i remove this recreation of transcript
        let mut t = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof.as_slice());
        let comm_sk_rho_halo2 = get_the_only_precommitted_col_comm(verifying_key, &mut t).unwrap();
        // TODO: Remove from self
        assert_eq!(comm_sk_rho_halo2, self.comm_sk_rho_halo2);

        let mut bases_halo2 = Vec::with_capacity(3 + NUM_CHUNKS + num_blindings_halo2);
        bases_halo2.push(params.g_lagrange[PRECOMMITTED_SK_IDX]);
        bases_halo2.push(params.g_lagrange[PRECOMMITTED_RHO_IDX]);
        bases_halo2.push(params.g_lagrange[PRECOMMITTED_RHO_SQ_IDX]);

        if T.is_some() {
            for i in 0..NUM_CHUNKS {
                bases_halo2.push(params.g_lagrange[PRECOMMITTED_CHUNKS_START_IDX+i]);
            }
        }
        for i in 0..(num_blindings_halo2 -1) {
            bases_halo2.push(params.g_lagrange[usable_rows+i]);
        }
        bases_halo2.push(params.w);

        self.resp_comm_sk_rho_halo2.challenge_contribution(&mut transcript_writer)?;

        let combined_s_commitment = if let Some(enc_rand) = &self.encrypted_randomness {
            let powers = powers_of_base::<G::ScalarExt, CHUNK_BITS, NUM_CHUNKS>();
            let encs = enc_rand
                .ciphertexts
                .iter()
                .map(|c| c.encrypted)
                .collect::<Vec<_>>();

            let enc_pairs = encs.iter().zip(powers.iter()).map(|(enc, power)| (*power, enc.to_curve())).collect::<Vec<_>>();
            let combined_s_commitment = multiexp_vartime(&enc_pairs).to_affine();

            let pk_T = T.as_ref().unwrap().0;
            let h = T.as_ref().unwrap().2;
            enc_rand.resp_combined_s.challenge_contribution(
                &pk_T,
                &h,
                &combined_s_commitment,
                &mut transcript_writer,
            )?;
            Some(combined_s_commitment)
        } else {
            None
        };

        let verifier_challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);
        println!("verifier_challenge {:?}", verifier_challenge);

        self.resp_acc_comm
            .verify(
                &reduced_acc_comm,
                &account_comm_key.current_rho_gen(),
                &account_comm_key.randomness_gen(),
                &verifier_challenge,
            )
            .map_err(|_| {
                Error::ProofVerificationError("Account commitment verification failed".to_string())
            })?;

        self.resp_initial_nullifier
            .verify(
                &self.initial_nullifier,
                &account_comm_key.rho_gen(),
                &verifier_challenge,
            )
            .map_err(|_| {
                Error::ProofVerificationError("Initial nullifier verification failed".to_string())
            })?;

        self.resp_pk
            .verify(pk, &account_comm_key.sk_gen(), &verifier_challenge)
            .map_err(|_| {
                Error::ProofVerificationError("Public key verification failed".to_string())
            })?;

        self.resp_comm_sk_rho_halo2.verify(&bases_halo2, &comm_sk_rho_halo2, &verifier_challenge)?;

        if self.resp_comm_sk_rho_halo2.s[0] != self.resp_pk.response {
            return Err(Error::ProofVerificationError(
                "Secret key mismatch between BP commitment and public key".to_string(),
            ));
        }
        if self.resp_comm_sk_rho_halo2.s[1] != self.resp_initial_nullifier.response {
            return Err(Error::ProofVerificationError(
                "Initial rho mismatch between BP commitment and initial nullifier".to_string(),
            ));
        }
        if self.resp_comm_sk_rho_halo2.s[2] != self.resp_acc_comm.response1 {
            return Err(Error::ProofVerificationError(
                "Rho mismatch between account and BP commitment".to_string(),
            ));
        }

        if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            // unwrap is fine as its already checked in the beginning
            let enc_rand = self.encrypted_randomness.as_ref().unwrap();
            for i in 0..NUM_CHUNKS {
                enc_rand.resp_eph_pk[i]
                    .verify(
                        &enc_rand.ciphertexts[i].eph_pk,
                        enc_key_gen,
                        &verifier_challenge,
                    )
                    .map_err(|_| {
                        Error::ProofVerificationError(
                            "Encrypted randomness verification failed".to_string(),
                        )
                    })?;

                enc_rand.resp_encrypted[i]
                    .verify(
                        &enc_rand.ciphertexts[i].encrypted,
                        pk_T,
                        enc_gen,
                        &verifier_challenge,
                    )
                    .map_err(|_| {
                        Error::ProofVerificationError(
                            "Encrypted randomness verification failed".to_string(),
                        )
                    })?;

                if enc_rand.resp_eph_pk[i].response != enc_rand.resp_encrypted[i].response1 {
                    return Err(Error::ProofVerificationError(
                        "Mismatch in combined encryption randomness".to_string(),
                    ));
                }

                if self.resp_comm_sk_rho_halo2.s[3+i] != enc_rand.resp_encrypted[i].response2 {
                    return Err(Error::ProofVerificationError(
                        format!("Mismatch in {i}-th commitment randomness chunk"),
                    ));
                }
            }

            enc_rand
                .resp_combined_s
                .verify(
                    &combined_s_commitment.unwrap(),
                    pk_T,
                    enc_gen,
                    &verifier_challenge,
                )
                .map_err(|_| {
                    Error::ProofVerificationError(
                        "Combined randomness verification failed".to_string(),
                    )
                })?;

            if enc_rand.resp_combined_s.response2 != self.resp_acc_comm.response2 {
                return Err(Error::ProofVerificationError(
                    "Mismatch in commitment randomness".to_string(),
                ));
            }
        }

        Ok(())
    }
}

impl<G: AffineSerializable, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    EncryptedRandomness<G, CHUNK_BITS, NUM_CHUNKS>
{
    pub fn decrypt(&self, sk_T: &G::ScalarExt, enc_gen: G::Curve) -> Result<G::ScalarExt> {
        let max = 1_u64 << CHUNK_BITS;
        let chunks = self
            .ciphertexts
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let e = c.decrypt(sk_T).to_curve();
                // TODO: This can be optimized as discrete log with same base is being computed
                solve_discrete_log_bsgs_alt(max, enc_gen, e)
                    .map(|d| G::Scalar::from(d))
                    .ok_or_else(|| Error::SolvingDiscreteLogFailed(i))
            })
            .collect::<Vec<_>>();
        let powers = powers_of_base::<G::ScalarExt, CHUNK_BITS, NUM_CHUNKS>();
        let mut reconstructed = G::ScalarExt::ZERO;
        for (i, c) in chunks.into_iter().enumerate() {
            reconstructed += c? * powers[i];
        }
        Ok(reconstructed)
    }
}

/// Decomposes a field element into base 2^BASE_BITS with NUM_DIGITS digits in total.
pub fn digits<F: PrimeField + PrimeFieldBits, const BASE_BITS: usize, const NUM_DIGITS: usize>(
    scalar: F,
) -> ([F; NUM_DIGITS], [u64; NUM_DIGITS]) {
    let mut chunks = [F::ZERO; NUM_DIGITS];
    let mut chunks_as_u64 = [0; NUM_DIGITS];
    let bits = scalar.to_le_bits();
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
    let mut powers = [F::ZERO; NUM_DIGITS];
    let base = F::from(1u64 << BASE_BITS);
    for i in 0..NUM_DIGITS {
        if i == 0 {
            powers[i] = F::ONE;
        } else {
            powers[i] = powers[i - 1] * base;
        }
    }
    powers
}

#[cfg(test)]
pub mod tests {
    use std::time::Instant;
    use ark_std::UniformRand;
    use super::*;
    use ff::Field;
    use group::cofactor::CofactorCurveAffine;
    use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
    use halo2_proofs::plonk::{keygen_pk, keygen_vk};
    use pasta_curves::pallas;
    use pasta_curves::pallas::Scalar as Fr;
    use crate::account::tests::setup_comm_key;
    use crate::{keygen_enc, keygen_sig};
    use crate::circuits::registration::{AccountRegCircuit, AccountRegWithEncCircuit};

    #[test]
    fn registration_without_pk_T() {
        let mut rng = rand::thread_rng();

        // Setup begins

        let account_comm_key = setup_comm_key(&mut rng);

        let asset_id = 1;

        // Investor creates keys
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let k = 6;

        let empty_circuit = AccountRegCircuit::<pallas::Scalar>::default();
        let params = Params::<pallas::Affine>::new(k);
        let snark_vk = keygen_vk(&params, &empty_circuit).unwrap();
        let snark_pk = keygen_pk(&params, snark_vk.clone(), &empty_circuit).unwrap();

        let clock = Instant::now();
        let nullifier_gen_counter = 10;
        let account = AccountState::new(&mut rng, sk.0, asset_id, nullifier_gen_counter).unwrap();
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
            &params,
            &snark_pk,
            None,
        )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        reg_proof
            .verify(
                &pk.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key,
                &params,
                &snark_vk,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For reg. txn");
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
        println!("Proof size {}", reg_proof.snark_proof.len());
    }

    #[test]
    fn registration_with_pk_T() {
        let mut rng = rand::thread_rng();

        // Setup begins

        const CHUNK_BITS: usize = 48;
        const NUM_CHUNKS: usize = 6;

        // Create public params (generators, etc)
        let account_comm_key = setup_comm_key(&mut rng);

        let asset_id = 1;

        // Investor creates keys
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();
        let (sk_T, pk_T) = keygen_enc(&mut rng, enc_key_gen);

        let k = 7;

        let empty_circuit = AccountRegWithEncCircuit::<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >::new_default(NUM_WORDS);
        let params = Params::<pallas::Affine>::new(k);
        let snark_vk = keygen_vk(&params, &empty_circuit).unwrap();
        let snark_pk = keygen_pk(&params, snark_vk.clone(), &empty_circuit).unwrap();

        let clock = Instant::now();
        let nullifier_gen_counter = 10;
        let mut account = AccountState::new(&mut rng, sk.0, asset_id, nullifier_gen_counter).unwrap();
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
            &params,
            &snark_pk,
            Some((pk_T.0, enc_key_gen, enc_gen)),
        )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        reg_proof
            .verify(
                &pk.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key,
                &params,
                &snark_vk,
                Some((pk_T.0, enc_key_gen, enc_gen)),
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For reg. txn with {NUM_CHUNKS} chunks each of {CHUNK_BITS} bits, and LIMB_BITS={LIMB_BITS}, NUM_WORDS={NUM_WORDS}");
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
        println!("Proof size {}", reg_proof.snark_proof.len());

        // This will take a long time to decrypt
        let clock = Instant::now();
        assert_eq!(
            account.randomness,
            reg_proof
                .encrypted_randomness
                .unwrap()
                .decrypt(&sk_T.0, enc_gen.to_curve())
                .unwrap()
        );
        println!("decryption time = {:?}", clock.elapsed());
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
        let mut reconstructed = Fr::ZERO;
        for i in 0..NUM_CHUNKS {
            reconstructed += d[i] * powers[i];
        }
        assert_eq!(reconstructed, val);

        const B: usize = 48;
        const N: usize = 6;
        let powers = powers_of_base::<Fr, B, N>();
        for _ in 0..100 {
            let val = Fr::random(&mut rng);
            let (d, u) = digits::<Fr, B, N>(val);
            let mut reconstructed = Fr::ZERO;
            for i in 0..N {
                reconstructed += d[i] * powers[i];
                assert_eq!(d[i], Fr::from(u[i]))
            }
            assert_eq!(reconstructed, val);
        }
    }
}
