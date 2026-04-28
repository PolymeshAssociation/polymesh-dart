use crate::account::state::AccountStateCommitment;
use crate::account::{AccountCommitmentKeyTrait, AccountState};
use crate::add_to_transcript;
use crate::auth_proofs::{AuthProofOnlySks, AuthProofOnlySksProtocol};
use crate::discrete_log::solve_discrete_log_bsgs;
use crate::error::*;
use crate::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc_given_sk, keygen_sig_given_sk};
use crate::poseidon_impls::poseidon_2::Poseidon_hash_2_constraints_simple;
use crate::poseidon_impls::poseidon_2::params::Poseidon2Params;
use crate::util::bp_gens_for_vec_commitment;
use crate::{ACCOUNT_COMMITMENT_LABEL, ASSET_ID_LABEL, ID_LABEL, NONCE_LABEL, PK_LABEL};
use crate::{AUTH_PROOF_LABEL, TXN_CHALLENGE_LABEL};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::BigInteger;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::string::ToString;
use ark_std::{UniformRand, vec, vec::Vec};
use bulletproofs::r1cs::{
    ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, VerificationTuple, Verifier,
    add_verification_tuple_to_rmc, verify_given_verification_tuple,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use core::mem;
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::aliases::FullDigest;
use dock_crypto_utils::elgamal::Ciphertext;
use dock_crypto_utils::ff::inner_product;
use dock_crypto_utils::hashing_utils::hash_to_field;
use dock_crypto_utils::msm::multiply_field_elems_with_same_group_elem;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, NullifierSkGenCounter, SkGenCounter};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment,
    PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::{Zeroize, ZeroizeOnDrop};

pub const PK_T_LABEL: &'static [u8; 4] = b"pk_t";
pub const PK_T_GEN_LABEL: &'static [u8; 8] = b"pk_t_gen";
pub const ENC_PK_LABEL: &'static [u8; 6] = b"pk_enc";

// A non-split (single prover) proof proves that the account commitment is correctly formed and that prover knows the
// affirmation and encryption secret keys, nullifier secret key, rho, commitment randomness, i.e. knowledge of opening
// of a commitment of the form `C = G_{aff} * sk + G_{enc} * sk_enc + G_i * rho + G_j * s + ....`
//
// A split proof is created by 2 provers, one prover (more secure device like ledger) knows the secret keys (might know other witnesses)
// and second prover does not know secret keys but knows other witnesses. The split proof is then combination of 2 proofs, first prover's
// proof of knowledge of secret keys in the public keys and the second prover's proof of knowledge of other witnesses in `C' = G_i * rho + G_j * s + ....`
// Now the verifier can check that `C = C' + pk_aff + pk_enc` as `pk_aff(=G_{aff} * sk)` and `pk_enc(=G_{enc} * sk_enc)` are public

/// Proof of encrypted randomness. The randomness is broken into `NUM_CHUNKS` chunks of `CHUNK_BITS` bits each
// TODO: Check if i can use Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf).
// The problem is that response of all chunks is aggregated in one value so tying it with BP is not straightforward. So need to check if aggregating
// those responses and comparing is safe
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EncryptedScalar<G: AffineRepr, const CHUNK_BITS: usize = 48, const NUM_CHUNKS: usize = 6>
{
    pub ciphertexts: [Ciphertext<G>; NUM_CHUNKS],
    /// For relation `g * r_i`
    pub resp_eph_pk: [PokDiscreteLog<G>; NUM_CHUNKS],
    /// For relation `pk_T * r_i + h * s_i`
    pub resp_encrypted: [PartialPokPedersenCommitment<G>; NUM_CHUNKS],
    /// For Pedersen commitment to the weighted scalar and chunks. The weighted chunks equals the scalar
    pub resp_combined_s: Partial1PokPedersenCommitment<G>,
}

/// Present only when `T` (encryption target pk) is provided for the registration
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EncryptionForRegistration<
    G: AffineRepr,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    /// Combined Bulletproof vector commitment to `[s_chunks..., rho_chunks...]`
    pub comm_s_rho_chunks_bp: G,
    pub t_comm_s_rho_chunks_bp: G,
    pub resp_comm_s_rho_chunks_bp: SchnorrResponse<G>,
    /// Called `uppercase Omega` in the report
    pub encrypted_randomness: EncryptedScalar<G, CHUNK_BITS, NUM_CHUNKS>,
    /// Encryption of `rho` (the nullifier secret) for `pk_T`
    pub encrypted_rho: EncryptedScalar<G, CHUNK_BITS, NUM_CHUNKS>,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RegTxnWithoutSkProof<
    G: AffineRepr,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    pub t_comm: G,
    pub resp_comm: SchnorrResponse<G>,
    /// `N = current_rho_gen * rho`, called the "initial nullifier".
    pub initial_nullifier: G,
    /// Proof of knowledge of `rho` in `initial_nullifier = current_rho_gen * rho`
    pub resp_initial_nullifier: PartialPokDiscreteLog<G>,
    /// Bulletproof vector commitment to `rho_randomness, rho, current_rho`
    pub comm_rho_bp: G,
    pub t_comm_rho_bp: G,
    pub resp_comm_rho_bp: PartialSchnorrResponse<G>,
    pub proof: Option<R1CSProof<G>>,
    /// Present only when `T` (trusted party for force transfer) is provided for the registration
    pub encryption_for_T: Option<EncryptionForRegistration<G, CHUNK_BITS, NUM_CHUNKS>>,
}

/// This is the proof for user registering its (signing) public key for an asset. Report section 5.1.3, called "Account Registration"
/// We could register both signing and encryption keys by modifying this proof even though the encryption isn't used in account commitment.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RegTxnProof<G: AffineRepr, const CHUNK_BITS: usize = 48, const NUM_CHUNKS: usize = 6> {
    pub partial: RegTxnWithoutSkProof<G, { CHUNK_BITS }, { NUM_CHUNKS }>,
    pub auth_proof: AuthProofOnlySks<G>,
}

/// Prover-side protocol state for the partial (non-auth) portion of RegTxnProof.
/// Holds Schnorr commitments, protocol objects, and witnesses needed for `gen_proof`.
pub struct RegTxnWithoutSkProtocol<
    G: AffineRepr,
    const CHUNK_BITS: usize = 48,
    const NUM_CHUNKS: usize = 6,
> {
    comm_protocol: SchnorrCommitment<G>,
    init_null_protocol: PokDiscreteLogProtocol<G>,
    t_comm_rho_bp: SchnorrCommitment<G>,
    initial_nullifier: G,
    comm_rho_bp: G,
    rho: G::ScalarField,
    current_rho: G::ScalarField,
    randomness: G::ScalarField,
    current_randomness: G::ScalarField,
    com_rho_bp_blinding: G::ScalarField,
    rho_randomness: G::ScalarField,
    // Encryption state (present only when T is provided)
    enc_state: Option<RegTxnEncryptionProtocolState<G, CHUNK_BITS, NUM_CHUNKS>>,
}

/// Holds the encryption-related protocol state for registration when T is provided.
struct RegTxnEncryptionProtocolState<
    G: AffineRepr,
    const CHUNK_BITS: usize,
    const NUM_CHUNKS: usize,
> {
    s_eph_proto: Vec<PokDiscreteLogProtocol<G>>,
    s_enc_proto: Vec<PokPedersenCommitmentProtocol<G>>,
    s_ciphertexts: Vec<Ciphertext<G>>,
    s_chunks: [G::ScalarField; NUM_CHUNKS],
    rho_eph_proto: Vec<PokDiscreteLogProtocol<G>>,
    rho_enc_proto: Vec<PokPedersenCommitmentProtocol<G>>,
    rho_ciphertexts: Vec<Ciphertext<G>>,
    rho_chunks: [G::ScalarField; NUM_CHUNKS],
    t_comm_s_rho_chunks_bp: SchnorrCommitment<G>,
    combined_s_proto: PokPedersenCommitmentProtocol<G>,
    combined_rho_proto: PokPedersenCommitmentProtocol<G>,
    comm_s_rho_chunks_bp: G,
    com_s_rho_bp_blinding: G::ScalarField,
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnWithoutSkProtocol<G, CHUNK_BITS, NUM_CHUNKS>
{
    const CHECK_CHUNK_BITS: () = assert!(
        CHUNK_BITS <= 48
            && ((<G::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize + CHUNK_BITS - 1)
                / CHUNK_BITS
                == NUM_CHUNKS)
    );

    /// Initialise the partial protocol. Takes `AccountState` (no secret keys).
    /// After calling this, the caller should add auth challenge contribution to the transcript
    /// before deriving the challenge.
    pub fn init_with_given_prover<R: CryptoRngCore>(
        rng: &mut R,
        pk_aff: G,
        pk_enc: G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        rho_randomness: G::ScalarField,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: &impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        prover: &mut Prover<MerlinTranscript, G>,
    ) -> Result<Self> {
        let _ = Self::CHECK_CHUNK_BITS;

        ensure_correct_registration_state(account)?;
        let mut transcript_ref = prover.transcript();
        add_to_transcript!(
            transcript_ref,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            account.asset_id,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk_aff,
            ENC_PK_LABEL,
            pk_enc,
            ID_LABEL,
            account.id
        );

        // D = pk_aff + pk_enc + g_k * asset_id + g_l * id
        let D = pk_aff.into_group()
            + pk_enc.into_group()
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(account.asset_id))
            + (account_comm_key.id_gen() * account.id);

        let mut rho_blinding = G::ScalarField::rand(rng);
        let mut rho_sq_blinding = G::ScalarField::rand(rng);
        let mut s_blinding = G::ScalarField::rand(rng);
        let mut s_sq_blinding = G::ScalarField::rand(rng);

        let reduced_acc_comm = (account_commitment.0.into_group() - D).into_affine();
        let comm_protocol = SchnorrCommitment::new(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
                account_comm_key.current_randomness_gen(),
            ],
            vec![rho_blinding, rho_sq_blinding, s_blinding, s_sq_blinding],
        );
        comm_protocol.challenge_contribution(&mut transcript_ref)?;
        reduced_acc_comm.serialize_compressed(&mut transcript_ref)?;

        // N = current_rho_gen * rho (initial nullifier)
        let initial_nullifier = (account_comm_key.current_rho_gen() * account.rho).into_affine();
        let init_null_protocol = PokDiscreteLogProtocol::init(
            account.rho,
            rho_blinding,
            &account_comm_key.current_rho_gen(),
        );
        init_null_protocol.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &initial_nullifier,
            &mut transcript_ref,
        )?;

        // Encryption protocols (if T is provided)
        let mut enc_prep = if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            let (s_chunks, s_chunks_as_u64) =
                digits::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>(account.randomness);
            let encs = G::Group::normalize_batch(&multiply_field_elems_with_same_group_elem(
                enc_gen.into_group(),
                &s_chunks,
            ));
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

            let mut eph_proto = Vec::with_capacity(NUM_CHUNKS);
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
                    &mut transcript_ref,
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
                    &mut transcript_ref,
                )?;
            }

            let (rho_chunks, rho_chunks_as_u64) =
                digits::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>(account.rho);
            let rho_encs = G::Group::normalize_batch(&multiply_field_elems_with_same_group_elem(
                enc_gen.into_group(),
                &rho_chunks,
            ));
            let rho_enc_rands = (0..NUM_CHUNKS)
                .map(|_| G::ScalarField::rand(rng))
                .collect::<Vec<_>>();
            let rho_chunks_blindings = (0..NUM_CHUNKS)
                .map(|_| G::ScalarField::rand(rng))
                .collect::<Vec<_>>();
            let rho_enc_rands_blindings = (0..NUM_CHUNKS)
                .map(|_| G::ScalarField::rand(rng))
                .collect::<Vec<_>>();
            let rho_ciphertexts = (0..NUM_CHUNKS)
                .map(|i| {
                    Ciphertext::new_given_randomness(
                        &rho_encs[i],
                        &rho_enc_rands[i],
                        pk_T,
                        enc_key_gen,
                    )
                })
                .collect::<Vec<_>>();

            let mut rho_eph_proto = Vec::with_capacity(NUM_CHUNKS);
            let mut rho_enc_proto = Vec::with_capacity(NUM_CHUNKS);
            for i in 0..NUM_CHUNKS {
                rho_eph_proto.push(PokDiscreteLogProtocol::init(
                    rho_enc_rands[i],
                    rho_enc_rands_blindings[i],
                    enc_key_gen,
                ));
                rho_eph_proto[i].challenge_contribution(
                    &enc_key_gen,
                    &rho_ciphertexts[i].eph_pk,
                    &mut transcript_ref,
                )?;
                rho_enc_proto.push(PokPedersenCommitmentProtocol::init(
                    rho_enc_rands[i],
                    rho_enc_rands_blindings[i],
                    pk_T,
                    rho_chunks[i],
                    rho_chunks_blindings[i],
                    enc_gen,
                ));
                rho_enc_proto[i].challenge_contribution(
                    pk_T,
                    enc_gen,
                    &rho_ciphertexts[i].encrypted,
                    &mut transcript_ref,
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
                rho_chunks,
                rho_chunks_as_u64,
                rho_enc_rands,
                rho_ciphertexts,
                rho_chunks_blindings,
                rho_eph_proto,
                rho_enc_proto,
            ))
        } else {
            None
        };

        // BP commitment for rho stuff
        let com_rho_bp_blinding = G::ScalarField::rand(rng);
        let (comm_rho_bp, vars) = prover.commit_vec(
            &[
                rho_randomness,
                account.rho,
                account.current_rho,
                account.randomness,
                account.current_randomness,
            ],
            com_rho_bp_blinding,
            &leaf_level_bp_gens,
        );
        RegTxnWithoutSkProof::<G, CHUNK_BITS, NUM_CHUNKS>::enforce_constraints(
            prover,
            account.asset_id,
            counter,
            vars,
            poseidon_config,
        )?;

        let rho_randomness_blinding = G::ScalarField::rand(rng);
        let t_comm_rho_bp = SchnorrCommitment::new(
            &RegTxnWithoutSkProof::<G, CHUNK_BITS, NUM_CHUNKS>::bp_gens_for_comm_rho(
                leaf_level_pc_gens,
                leaf_level_bp_gens,
            ),
            vec![
                G::ScalarField::rand(rng),
                rho_randomness_blinding,
                rho_blinding,
                rho_sq_blinding,
                s_blinding,
                s_sq_blinding,
            ],
        );

        // Commit to all chunks of s and rho in a single vector commitment
        let (comm_s_rho_chunks_bp, com_s_rho_bp_blinding) = if let Some((
            s_chunks,
            s_chunks_as_u64,
            _,
            _,
            _,
            _,
            _,
            rho_chunks,
            rho_chunks_as_u64,
            _,
            _,
            _,
            _,
            _,
        )) = &mut enc_prep
        {
            let com_s_rho_bp_blinding = G::ScalarField::rand(rng);
            let combined_chunks: Vec<G::ScalarField> =
                s_chunks.iter().chain(rho_chunks.iter()).copied().collect();
            let (comm_s_rho_bp, vars) =
                prover.commit_vec(&combined_chunks, com_s_rho_bp_blinding, &leaf_level_bp_gens);
            for (i, var) in vars.into_iter().enumerate() {
                if i < NUM_CHUNKS {
                    let chunk = mem::take(&mut s_chunks_as_u64[i]);
                    range_proof(prover, var.into(), Some(chunk as u128), CHUNK_BITS)?;
                } else {
                    let chunk = mem::take(&mut rho_chunks_as_u64[i - NUM_CHUNKS]);
                    range_proof(prover, var.into(), Some(chunk as u128), CHUNK_BITS)?;
                }
            }
            (Some(comm_s_rho_bp), Some(com_s_rho_bp_blinding))
        } else {
            (None, None)
        };

        let mut transcript_ref = prover.transcript();
        t_comm_rho_bp.challenge_contribution(&mut transcript_ref)?;

        // Chunks commitment t-values and combined protos
        let combined_enc_data = if let Some((
            _,
            _,
            enc_rands,
            _,
            s_chunks_blindings,
            _,
            _,
            _,
            _,
            rho_enc_rands,
            _,
            rho_chunks_blindings,
            _,
            _,
        )) = &mut enc_prep
        {
            let mut blindings = vec![G::ScalarField::rand(rng)];
            for i in 0..NUM_CHUNKS {
                let b = mem::take(&mut s_chunks_blindings[i]);
                blindings.push(b);
            }
            for i in 0..NUM_CHUNKS {
                let b = mem::take(&mut rho_chunks_blindings[i]);
                blindings.push(b);
            }
            let t_comm_s_rho_chunks_bp = SchnorrCommitment::new(
                &RegTxnWithoutSkProof::<G, CHUNK_BITS, NUM_CHUNKS>::bp_gens_for_comm_s_rho_chunks(
                    leaf_level_pc_gens,
                    leaf_level_bp_gens,
                ),
                blindings,
            );
            t_comm_s_rho_chunks_bp.challenge_contribution(&mut transcript_ref)?;

            let powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();
            let mut combined_enc_rand =
                inner_product::<G::ScalarField>(enc_rands.as_slice(), &powers);
            let pk_T = T.as_ref().unwrap().0;
            let h = T.as_ref().unwrap().2;
            let combined_s_commitment =
                (pk_T * combined_enc_rand + h * account.randomness).into_affine();

            for i in 0..NUM_CHUNKS {
                let mut e = mem::take(&mut enc_rands[i]);
                Zeroize::zeroize(&mut e);
            }

            let combined_s_proto = PokPedersenCommitmentProtocol::init(
                combined_enc_rand,
                G::ScalarField::rand(rng),
                &pk_T,
                account.randomness,
                s_blinding,
                &h,
            );

            s_blinding.zeroize();
            s_sq_blinding.zeroize();
            combined_enc_rand.zeroize();

            combined_s_proto.challenge_contribution(
                &pk_T,
                &h,
                &combined_s_commitment,
                &mut transcript_ref,
            )?;

            let rho_powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();
            let mut combined_rho_enc_rand =
                inner_product::<G::ScalarField>(rho_enc_rands.as_slice(), &rho_powers);
            let combined_rho_commitment =
                (pk_T * combined_rho_enc_rand + h * account.rho).into_affine();

            for i in 0..NUM_CHUNKS {
                let mut e = mem::take(&mut rho_enc_rands[i]);
                Zeroize::zeroize(&mut e);
            }

            let combined_rho_proto = PokPedersenCommitmentProtocol::init(
                combined_rho_enc_rand,
                G::ScalarField::rand(rng),
                &pk_T,
                account.rho,
                rho_blinding,
                &h,
            );

            rho_blinding.zeroize();
            rho_sq_blinding.zeroize();
            combined_rho_enc_rand.zeroize();

            combined_rho_proto.challenge_contribution(
                &pk_T,
                &h,
                &combined_rho_commitment,
                &mut transcript_ref,
            )?;

            Some((t_comm_s_rho_chunks_bp, combined_s_proto, combined_rho_proto))
        } else {
            None
        };

        // Now consume enc_prep to build the encryption state
        let enc_state = match (enc_prep, combined_enc_data) {
            (
                Some((
                    s_chunks,
                    _,
                    _,
                    s_ciphertexts,
                    _,
                    s_eph_proto,
                    s_enc_proto,
                    rho_chunks,
                    _,
                    _,
                    rho_ciphertexts,
                    _,
                    rho_eph_proto,
                    rho_enc_proto,
                )),
                Some((t_comm_s_rho_chunks_bp, combined_s_proto, combined_rho_proto)),
            ) => Some(RegTxnEncryptionProtocolState {
                s_eph_proto,
                s_enc_proto,
                s_ciphertexts,
                s_chunks,
                rho_eph_proto,
                rho_enc_proto,
                rho_ciphertexts,
                rho_chunks,
                t_comm_s_rho_chunks_bp,
                combined_s_proto,
                combined_rho_proto,
                comm_s_rho_chunks_bp: comm_s_rho_chunks_bp.unwrap(),
                com_s_rho_bp_blinding: com_s_rho_bp_blinding.unwrap(),
            }),
            _ => None,
        };

        Ok(Self {
            comm_protocol,
            init_null_protocol,
            t_comm_rho_bp,
            initial_nullifier,
            comm_rho_bp,
            rho: account.rho,
            current_rho: account.current_rho,
            randomness: account.randomness,
            current_randomness: account.current_randomness,
            com_rho_bp_blinding,
            rho_randomness,
            enc_state,
        })
    }

    /// Generate the partial proof given a challenge. Consumes the protocol state.
    pub fn gen_proof(
        self,
        challenge: &G::ScalarField,
    ) -> Result<RegTxnWithoutSkProof<G, CHUNK_BITS, NUM_CHUNKS>> {
        let resp_comm = self.comm_protocol.response(
            &[
                self.rho,
                self.current_rho,
                self.randomness,
                self.current_randomness,
            ],
            challenge,
        )?;

        let resp_initial_nullifier = self.init_null_protocol.gen_partial_proof();

        let mut wits = BTreeMap::new();
        wits.insert(0, self.com_rho_bp_blinding);
        wits.insert(1, self.rho_randomness);
        let resp_comm_rho_bp = self.t_comm_rho_bp.partial_response(wits, challenge)?;

        let encryption_for_T = if let Some(enc) = self.enc_state {
            let mut resp_eph_pk = Vec::with_capacity(NUM_CHUNKS);
            let mut resp_encrypted = Vec::with_capacity(NUM_CHUNKS);
            for (eph, enc_p) in enc.s_eph_proto.into_iter().zip(enc.s_enc_proto.into_iter()) {
                resp_eph_pk.push(eph.gen_proof(challenge));
                resp_encrypted.push(enc_p.gen_partial_proof());
            }
            let resp_combined_s = enc.combined_s_proto.gen_partial1_proof(challenge);

            let enc_rand = EncryptedScalar::<G, CHUNK_BITS, NUM_CHUNKS> {
                ciphertexts: enc.s_ciphertexts.try_into().unwrap(),
                resp_eph_pk: resp_eph_pk.try_into().unwrap(),
                resp_encrypted: resp_encrypted.try_into().unwrap(),
                resp_combined_s,
            };

            let mut rho_resp_eph_pk = Vec::with_capacity(NUM_CHUNKS);
            let mut rho_resp_encrypted = Vec::with_capacity(NUM_CHUNKS);
            for (eph, enc_p) in enc
                .rho_eph_proto
                .into_iter()
                .zip(enc.rho_enc_proto.into_iter())
            {
                rho_resp_eph_pk.push(eph.gen_proof(challenge));
                rho_resp_encrypted.push(enc_p.gen_partial_proof());
            }
            let resp_combined_rho = enc.combined_rho_proto.gen_partial1_proof(challenge);

            let enc_rho = EncryptedScalar::<G, CHUNK_BITS, NUM_CHUNKS> {
                ciphertexts: enc.rho_ciphertexts.try_into().unwrap(),
                resp_eph_pk: rho_resp_eph_pk.try_into().unwrap(),
                resp_encrypted: rho_resp_encrypted.try_into().unwrap(),
                resp_combined_s: resp_combined_rho,
            };

            let t_comm = enc.t_comm_s_rho_chunks_bp;
            let mut all_wits: Vec<G::ScalarField> = vec![enc.com_s_rho_bp_blinding];
            all_wits.extend_from_slice(&enc.s_chunks);
            all_wits.extend_from_slice(&enc.rho_chunks);
            let resp_s_rho_chunks = t_comm.response(&all_wits, challenge)?;
            Zeroize::zeroize(&mut all_wits);

            Some(EncryptionForRegistration {
                comm_s_rho_chunks_bp: enc.comm_s_rho_chunks_bp,
                t_comm_s_rho_chunks_bp: t_comm.t,
                resp_comm_s_rho_chunks_bp: resp_s_rho_chunks,
                encrypted_randomness: enc_rand,
                encrypted_rho: enc_rho,
            })
        } else {
            None
        };

        Ok(RegTxnWithoutSkProof {
            t_comm: self.comm_protocol.t,
            resp_comm,
            initial_nullifier: self.initial_nullifier,
            resp_initial_nullifier,
            comm_rho_bp: self.comm_rho_bp,
            t_comm_rho_bp: self.t_comm_rho_bp.t,
            resp_comm_rho_bp,
            encryption_for_T,
            proof: None,
        })
    }

    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk_aff: G,
        pk_enc: G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        rho_randomness: G::ScalarField,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: &impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<RegTxnWithoutSkProof<G, CHUNK_BITS, NUM_CHUNKS>> {
        let (proto, mut prover) = Self::init(
            rng,
            pk_aff,
            pk_enc,
            account,
            account_commitment,
            rho_randomness,
            counter,
            nonce,
            account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
        )?;

        let challenge_h = prover
            .transcript()
            .challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        let mut partial = proto.gen_proof(&challenge_h)?;

        let r1cs_proof = prover.prove_with_rng(leaf_level_bp_gens, rng)?;
        partial.proof = Some(r1cs_proof);

        Ok(partial)
    }

    pub fn init<'a, R: CryptoRngCore>(
        rng: &mut R,
        pk_aff: G,
        pk_enc: G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        rho_randomness: G::ScalarField,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: &impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &'a PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<(Self, Prover<'a, MerlinTranscript, G>)> {
        let transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut prover = Prover::new(leaf_level_pc_gens, transcript);

        let proto = Self::init_with_given_prover(
            rng,
            pk_aff,
            pk_enc,
            account,
            account_commitment,
            rho_randomness,
            counter,
            nonce,
            account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
            &mut prover,
        )?;

        Ok((proto, prover))
    }
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnWithoutSkProof<G, CHUNK_BITS, NUM_CHUNKS>
{
    /// Add the partial proof's challenge contribution to the verifier transcript.
    /// This must be called BEFORE auth challenge contribution and challenge derivation.
    pub fn challenge_contribution_with_verifier(
        &self,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: &impl AccountCommitmentKeyTrait<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        verifier: &mut Verifier<MerlinTranscript, G>,
    ) -> Result<()> {
        if T.is_none() ^ self.encryption_for_T.is_none() {
            return Err(Error::PkTAndEncryptedRandomnessInconsistent);
        }
        if self.resp_comm_rho_bp.responses.len() != 2 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                2,
                self.resp_comm_rho_bp.responses.len(),
            ));
        }
        if let Some(ref enc_for_T) = self.encryption_for_T {
            if enc_for_T.resp_comm_s_rho_chunks_bp.len() != (2 * NUM_CHUNKS + 1) {
                return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                    2 * NUM_CHUNKS + 1,
                    enc_for_T.resp_comm_s_rho_chunks_bp.len(),
                ));
            }
        }

        let mut transcript_ref = verifier.transcript();
        add_to_transcript!(
            transcript_ref,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            asset_id,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk_aff,
            ENC_PK_LABEL,
            pk_enc,
            ID_LABEL,
            id
        );

        // D = pk_aff + pk_enc + g_k * asset_id + g_l * id
        let D = pk_aff.into_group()
            + pk_enc.into_group()
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id))
            + (account_comm_key.id_gen() * id);
        let reduced_acc_comm = (account_commitment.0.into_group() - D).into_affine();

        self.t_comm.serialize_compressed(&mut transcript_ref)?;
        reduced_acc_comm.serialize_compressed(&mut transcript_ref)?;

        // N = current_rho_gen * rho
        self.resp_initial_nullifier.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &self.initial_nullifier,
            &mut transcript_ref,
        )?;

        // Encryption challenge contributions
        if let Some((pk_T, enc_key_gen_T, enc_gen)) = &T {
            let enc_for_T = self.encryption_for_T.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("Missing encryption data for T".to_string())
            })?;
            let enc_rand = &enc_for_T.encrypted_randomness;
            for i in 0..NUM_CHUNKS {
                enc_rand.resp_eph_pk[i].challenge_contribution(
                    enc_key_gen_T,
                    &enc_rand.ciphertexts[i].eph_pk,
                    &mut transcript_ref,
                )?;
                enc_rand.resp_encrypted[i].challenge_contribution(
                    pk_T,
                    enc_gen,
                    &enc_rand.ciphertexts[i].encrypted,
                    &mut transcript_ref,
                )?;
            }
            let enc_rho = &enc_for_T.encrypted_rho;
            for i in 0..NUM_CHUNKS {
                enc_rho.resp_eph_pk[i].challenge_contribution(
                    enc_key_gen_T,
                    &enc_rho.ciphertexts[i].eph_pk,
                    &mut transcript_ref,
                )?;
                enc_rho.resp_encrypted[i].challenge_contribution(
                    pk_T,
                    enc_gen,
                    &enc_rho.ciphertexts[i].encrypted,
                    &mut transcript_ref,
                )?;
            }
        }

        // BP commitment + constraints
        let vars = verifier.commit_vec(5, self.comm_rho_bp);
        RegTxnWithoutSkProof::<G, CHUNK_BITS, NUM_CHUNKS>::enforce_constraints(
            verifier,
            asset_id,
            counter,
            vars,
            poseidon_config,
        )?;

        // Chunks range proofs
        if let Some(ref enc_for_T) = self.encryption_for_T {
            let vars = verifier.commit_vec(2 * NUM_CHUNKS, enc_for_T.comm_s_rho_chunks_bp);
            debug_assert_eq!(vars.len(), 2 * NUM_CHUNKS);
            for var in vars {
                range_proof(verifier, var.into(), None, CHUNK_BITS)?;
            }
        }

        let mut transcript_ref = verifier.transcript();
        self.t_comm_rho_bp
            .serialize_compressed(&mut transcript_ref)?;

        // Chunks combined protos
        if let Some(ref enc_for_T) = self.encryption_for_T {
            let enc_rand = &enc_for_T.encrypted_randomness;
            enc_for_T
                .t_comm_s_rho_chunks_bp
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

            let enc_rho = &enc_for_T.encrypted_rho;
            let rho_encs = enc_rho
                .ciphertexts
                .iter()
                .map(|c| c.encrypted)
                .collect::<Vec<_>>();
            let combined_rho_commitment = G::Group::msm(&rho_encs, &powers)
                .map_err(Error::size_mismatch)?
                .into_affine();

            enc_rho.resp_combined_s.challenge_contribution(
                &pk_T,
                &h,
                &combined_rho_commitment,
                &mut transcript_ref,
            )?;
        }

        Ok(())
    }

    pub fn challenge_contribution(
        &self,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: &impl AccountCommitmentKeyTrait<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<Verifier<MerlinTranscript, G>> {
        let verifier_transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);
        self.challenge_contribution_with_verifier(
            id,
            pk_aff,
            pk_enc,
            asset_id,
            account_commitment,
            counter,
            nonce,
            account_comm_key,
            poseidon_config,
            T,
            &mut verifier,
        )?;
        Ok(verifier)
    }

    /// Verify the partial proof responses given a challenge.
    /// Auth proof verification is NOT done here.
    pub fn verify_with_challenge(
        &self,
        challenge: &G::ScalarField,
        account_comm_key: &impl AccountCommitmentKeyTrait<G>,
        pk_aff: G,
        pk_enc: G,
        id: G::ScalarField,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        T: Option<(G, G, G)>,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        if self.resp_comm.len() != 4 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                4,
                self.resp_comm.len(),
            ));
        }

        // D = pk_aff + pk_enc + g_k * asset_id + g_l * id
        let D = pk_aff.into_group()
            + pk_enc.into_group()
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id))
            + (account_comm_key.id_gen() * id);
        let reduced_acc_comm = (account_commitment.0.into_group() - D).into_affine();

        // Verify account commitment Schnorr
        let bases = vec![
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_comm_key.current_randomness_gen(),
        ];
        verify_schnorr_resp_or_rmc!(
            rmc,
            self.resp_comm,
            bases,
            reduced_acc_comm,
            self.t_comm,
            challenge,
        );

        // Verify BP commitment Schnorr
        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(2, self.resp_comm.0[0]);
        missing_resps.insert(3, self.resp_comm.0[1]);
        missing_resps.insert(4, self.resp_comm.0[2]);
        missing_resps.insert(5, self.resp_comm.0[3]);
        verify_partial_schnorr_resp_or_rmc!(
            rmc,
            self.resp_comm_rho_bp,
            RegTxnWithoutSkProof::<G, CHUNK_BITS, NUM_CHUNKS>::bp_gens_for_comm_rho(
                leaf_level_pc_gens,
                leaf_level_bp_gens,
            )
            .to_vec(),
            self.comm_rho_bp,
            self.t_comm_rho_bp,
            challenge,
            missing_resps,
        );

        // Verify initial nullifier
        verify_or_rmc_2!(
            rmc,
            self.resp_initial_nullifier,
            "Initial nullifier verification failed",
            self.initial_nullifier,
            account_comm_key.current_rho_gen(),
            challenge,
            &self.resp_comm.0[0]
        );

        // Verify encryption proofs
        if let Some((pk_T, enc_key_gen, enc_gen)) = &T {
            let enc_for_T = self.encryption_for_T.as_ref().unwrap();
            let enc_rand = &enc_for_T.encrypted_randomness;
            let resp_s_rho = &enc_for_T.resp_comm_s_rho_chunks_bp;
            for i in 0..NUM_CHUNKS {
                verify_or_rmc_2!(
                    rmc,
                    enc_rand.resp_eph_pk[i],
                    "Encrypted randomness verification failed",
                    enc_rand.ciphertexts[i].eph_pk,
                    *enc_key_gen,
                    challenge,
                );
                verify_or_rmc_3!(
                    rmc,
                    enc_rand.resp_encrypted[i],
                    "Encrypted randomness verification failed",
                    enc_rand.ciphertexts[i].encrypted,
                    *pk_T,
                    *enc_gen,
                    challenge,
                    &enc_rand.resp_eph_pk[i].response,
                    &resp_s_rho.0[i + 1],
                );
            }

            // Compute combined_s_commitment for verification
            let powers = powers_of_base::<G::ScalarField, CHUNK_BITS, NUM_CHUNKS>();
            let encs = enc_rand
                .ciphertexts
                .iter()
                .map(|c| c.encrypted)
                .collect::<Vec<_>>();
            let combined_s_commitment = G::Group::msm(&encs, &powers)
                .map_err(Error::size_mismatch)?
                .into_affine();
            verify_or_rmc_3!(
                rmc,
                enc_rand.resp_combined_s,
                "Combined randomness verification failed",
                combined_s_commitment,
                *pk_T,
                *enc_gen,
                challenge,
                &self.resp_comm.0[2],
            );

            // Verify rho encryption
            let enc_rho = &enc_for_T.encrypted_rho;
            for i in 0..NUM_CHUNKS {
                verify_or_rmc_2!(
                    rmc,
                    enc_rho.resp_eph_pk[i],
                    "Encrypted rho verification failed",
                    enc_rho.ciphertexts[i].eph_pk,
                    *enc_key_gen,
                    challenge,
                );
                verify_or_rmc_3!(
                    rmc,
                    enc_rho.resp_encrypted[i],
                    "Encrypted rho verification failed",
                    enc_rho.ciphertexts[i].encrypted,
                    *pk_T,
                    *enc_gen,
                    challenge,
                    &enc_rho.resp_eph_pk[i].response,
                    &resp_s_rho.0[NUM_CHUNKS + i + 1],
                );
            }

            // Single verify for the merged chunk commitment
            verify_schnorr_resp_or_rmc!(
                rmc,
                *resp_s_rho,
                RegTxnWithoutSkProof::<G, CHUNK_BITS, NUM_CHUNKS>::bp_gens_for_comm_s_rho_chunks(
                    leaf_level_pc_gens,
                    leaf_level_bp_gens,
                ),
                enc_for_T.comm_s_rho_chunks_bp,
                enc_for_T.t_comm_s_rho_chunks_bp,
                challenge,
            );

            // Compute combined_rho_commitment for verification
            let rho_encs = enc_rho
                .ciphertexts
                .iter()
                .map(|c| c.encrypted)
                .collect::<Vec<_>>();
            let combined_rho_commitment = G::Group::msm(&rho_encs, &powers)
                .map_err(Error::size_mismatch)?
                .into_affine();
            verify_or_rmc_3!(
                rmc,
                enc_rho.resp_combined_s,
                "Combined rho verification failed",
                combined_rho_commitment,
                *pk_T,
                *enc_gen,
                challenge,
                &self.resp_comm.0[0],
            );
        }

        Ok(())
    }
}

pub const REG_TXN_LABEL: &'static [u8; 12] = b"registration";

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnProof<G, CHUNK_BITS, NUM_CHUNKS>
{
    /// `pk_aff` is the affirmation public key
    /// `pk_enc` is the encryption public key
    /// `rho_randomness` is the random value used to derive `rho`
    /// `T` are the public key `pk_T`, generator used when creating key `pk_T` and the generator used to encrypt randomness chunk.
    /// This is intentionally kept different from the generator for randomness in account commitment to prevent anyone from
    /// learning the next nullifier
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        sk_enc: G::ScalarField,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        rho_randomness: G::ScalarField,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut prover = Prover::new(&leaf_level_pc_gens, transcript);
        let mut proof = Self::new_with_given_prover(
            rng,
            sk_aff,
            sk_enc,
            account,
            account_commitment,
            rho_randomness,
            counter,
            nonce,
            account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
            &mut prover,
        )?;

        let r1cs_proof = prover.prove_with_rng(leaf_level_bp_gens, rng)?;
        proof.partial.proof = Some(r1cs_proof);

        Ok(proof)
    }

    pub fn new_with_given_prover<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        sk_enc: G::ScalarField,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        rho_randomness: G::ScalarField,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        prover: &mut Prover<MerlinTranscript, G>,
    ) -> Result<Self> {
        let enc_key_gen = account_comm_key.sk_enc_gen();
        let aff_key_gen = account_comm_key.sk_gen();
        ensure_correct_sk(account, sk_aff, sk_enc, aff_key_gen, enc_key_gen)?;

        let pk_aff = account.pk_aff();
        let pk_enc = account.pk_enc();
        let partial_proto = RegTxnWithoutSkProtocol::init_with_given_prover(
            rng,
            pk_aff,
            pk_enc,
            account,
            account_commitment,
            rho_randomness,
            counter,
            nonce,
            &account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
            prover,
        )?;

        // Auth comes after all partial challenge contributions
        let mut transcript_ref = prover.transcript();
        let auth_protocol = AuthProofOnlySksProtocol::init(
            rng,
            sk_aff,
            sk_enc,
            &pk_aff,
            &pk_enc,
            &aff_key_gen,
            &enc_key_gen,
            &mut transcript_ref,
        )?;

        let challenge = prover
            .transcript()
            .challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let partial = partial_proto.gen_proof(&challenge)?;
        let auth_proof = auth_protocol.gen_proof(&challenge);

        Ok(Self {
            auth_proof,
            partial,
        })
    }

    /// Create a new verifier and verify the given proof
    /// `pk_aff` is the affirmation public key
    /// `pk_enc` is the encryption public key
    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let tuple = self.verify_and_return_tuples(
            id,
            pk_aff,
            pk_enc,
            asset_id,
            account_commitment,
            counter,
            nonce,
            account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
            rng,
            rmc.as_deref_mut(),
        )?;

        match rmc.as_mut() {
            Some(rmc) => {
                add_verification_tuple_to_rmc(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens, rmc)
                    .map_err(|e| e.into())
            }
            _ => verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens)
                .map_err(|e| e.into()),
        }
    }

    /// Create a new verifier and verify the given proof
    /// `pk_aff` is the affirmation public key
    /// `pk_enc` is the encryption public key
    pub fn verify_split<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let tuple = self.verify_split_and_return_tuples(
            rng,
            id,
            pk_aff,
            pk_enc,
            asset_id,
            account_commitment,
            counter,
            nonce,
            account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
            rmc.as_deref_mut(),
        )?;

        match rmc.as_mut() {
            Some(rmc) => {
                add_verification_tuple_to_rmc(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens, rmc)
                    .map_err(|e| e.into())
            }
            _ => verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens)
                .map_err(|e| e.into()),
        }
    }

    /// Create a new verifier and verify the given proof
    /// `pk_aff` is the affirmation public key
    /// `pk_enc` is the encryption public key
    pub fn verify_split_and_return_tuples<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<VerificationTuple<G>> {
        let mut verifier = self.partial.challenge_contribution(
            id,
            pk_aff,
            pk_enc,
            asset_id,
            &account_commitment,
            counter,
            nonce,
            &account_comm_key,
            poseidon_config,
            T,
        )?;

        let challenge_h_v = verifier
            .transcript()
            .challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v.serialize_compressed(&mut challenge_h_v_bytes)?;
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        let sk_gen = account_comm_key.sk_gen();
        let sk_enc_gen = account_comm_key.sk_enc_gen();
        self.auth_proof
            .verify(pk_aff, pk_enc, &ledger_nonce_v, &sk_gen, &sk_enc_gen, None)?;

        let mut auth_proof_bytes = Vec::new();
        self.auth_proof
            .serialize_compressed(&mut auth_proof_bytes)?;
        verifier
            .transcript()
            .append_message(AUTH_PROOF_LABEL, &auth_proof_bytes);
        let challenge_h_final_v = verifier
            .transcript()
            .challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        self.partial.verify_with_challenge(
            &challenge_h_final_v,
            &account_comm_key,
            pk_aff,
            pk_enc,
            id,
            asset_id,
            &account_commitment,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            None,
            rmc,
        )?;

        let bp_proof =
            self.partial.proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;
        let tuple = verifier.verification_scalars_and_points_with_rng(bp_proof, rng)?;
        Ok(tuple)
    }

    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<VerificationTuple<G>> {
        let verifier_transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);
        self.verify_sigma_protocols_and_enforce_constraints(
            id,
            pk_aff,
            pk_enc,
            asset_id,
            account_commitment,
            counter,
            nonce,
            account_comm_key,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            poseidon_config,
            T,
            &mut verifier,
            rmc,
        )?;

        let proof =
            self.partial.proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;
        let tuple = verifier.verification_scalars_and_points_with_rng(proof, rng)?;
        Ok(tuple)
    }

    pub fn verify_sigma_protocols_and_enforce_constraints(
        &self,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<G>,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
        T: Option<(G, G, G)>,
        verifier: &mut Verifier<MerlinTranscript, G>,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        // Partial challenge contribution (transcript)
        self.partial.challenge_contribution_with_verifier(
            id,
            pk_aff,
            pk_enc,
            asset_id,
            account_commitment,
            counter,
            nonce,
            &account_comm_key,
            poseidon_config,
            T,
            verifier,
        )?;

        // Auth challenge contribution (after all partial contributions)
        let enc_key_gen = account_comm_key.sk_enc_gen();
        let sk_gen = account_comm_key.sk_gen();
        let mut transcript_ref = verifier.transcript();
        self.auth_proof.challenge_contribution(
            &pk_aff,
            &pk_enc,
            &sk_gen,
            &enc_key_gen,
            &mut transcript_ref,
        )?;

        let challenge = transcript_ref.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        // Verify partial
        self.partial.verify_with_challenge(
            &challenge,
            &account_comm_key,
            pk_aff,
            pk_enc,
            id,
            asset_id,
            account_commitment,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            T,
            rmc.as_deref_mut(),
        )?;

        // Verify auth
        self.auth_proof.verify_given_challenge(
            &pk_aff,
            &pk_enc,
            &sk_gen,
            &enc_key_gen,
            &challenge,
            None,
        )?;

        Ok(())
    }
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    RegTxnWithoutSkProof<G, CHUNK_BITS, NUM_CHUNKS>
{
    fn enforce_constraints<CS: ConstraintSystem<G::ScalarField>>(
        cs: &mut CS,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        mut vars: Vec<Variable<G::ScalarField>>,
        poseidon_config: &Poseidon2Params<G::ScalarField>,
    ) -> Result<()> {
        let var_current_randomness = vars.pop().unwrap();
        let var_randomness = vars.pop().unwrap();
        let var_current_rho = vars.pop().unwrap();
        let var_rho = vars.pop().unwrap();
        let var_rho_randomness = vars.pop().unwrap();

        let lc_rho: LinearCombination<G::ScalarField> = var_rho.into();
        let lc_randomness: LinearCombination<G::ScalarField> = var_randomness.into();
        let combined = AccountState::<G>::concat_asset_id_counter(asset_id, counter);
        let c = LinearCombination::from(combined);
        let lc_rho_1 =
            Poseidon_hash_2_constraints_simple(cs, var_rho_randomness.into(), c, poseidon_config)?;
        cs.constrain(lc_rho_1 - lc_rho.clone());
        let (_, _, var_rho_sq_out) = cs.multiply(lc_rho.clone(), lc_rho);
        cs.constrain(var_rho_sq_out - var_current_rho);
        let (_, _, var_randomness_sq_out) = cs.multiply(lc_randomness.clone(), lc_randomness);
        cs.constrain(var_randomness_sq_out - var_current_randomness);
        Ok(())
    }

    fn bp_gens_for_comm_rho(
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
    ) -> [G; 6] {
        let mut gens = bp_gens_for_vec_commitment(5, leaf_level_bp_gens);
        [
            leaf_level_pc_gens.B_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ]
    }

    fn bp_gens_for_comm_s_rho_chunks(
        leaf_level_pc_gens: &PedersenGens<G>,
        leaf_level_bp_gens: &BulletproofGens<G>,
    ) -> Vec<G> {
        let mut g = Vec::with_capacity(2 * NUM_CHUNKS + 1);
        g.push(leaf_level_pc_gens.B_blinding);
        let mut gens = bp_gens_for_vec_commitment((2 * NUM_CHUNKS) as u32, leaf_level_bp_gens);
        for _ in 0..(2 * NUM_CHUNKS) {
            g.push(gens.next().unwrap());
        }
        g
    }
}

impl<G: AffineRepr, const CHUNK_BITS: usize, const NUM_CHUNKS: usize>
    EncryptedScalar<G, CHUNK_BITS, NUM_CHUNKS>
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

/*
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
    /// The second returned value is the `initial_nullifier` and called `N` in the report.
    /// This helps during account freezing to remove `g_i * rho` term from account state commitment.
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
    ) -> Result<(Self, Affine<G0>)> {
        ensure_correct_registration_state(account)?;

        let p_1 = (pk_T_gen * r_1).into_affine();
        let p_2 = (pk_T_gen * r_2).into_affine();
        let T_1 = (pk_T * r_1).into_affine();
        let T_2 = (pk_T * r_2).into_affine();
        let p_1_xy = p_1.xy().unwrap();
        let p_2_xy = p_2.xy().unwrap();
        let x_1 = p_1_xy.0;
        let y_1 = p_1_xy.1;
        let x_2 = p_2_xy.0;
        let y_2 = p_2_xy.1;

        // x_1 is rho
        // x_2 is randomness
        debug_assert_eq!(account.rho, x_1);
        debug_assert_eq!(account.randomness, x_2);

        let mut transcript = MerlinTranscript::new(REG_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            account.asset_id,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk,
            ID_LABEL,
            account.id,
            PK_T_LABEL,
            pk_T,
            PK_T_GEN_LABEL,
            pk_T_gen
        );

        let initial_nullifier = account.initial_nullifier(&account_comm_key);

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

        Ok((
            Self {
                T_1,
                T_2,
                resp_comm,
                resp_initial_nullifier,
                comm_bp,
                t_comm_bp: t_comm_bp.t,
                resp_comm_bp,
                resp_pk,
                resp_T_1,
                resp_T_2,
                proof,
            },
            initial_nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        id: G0::ScalarField,
        pk: &Affine<G0>,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment<Affine<G0>>,
        initial_nullifier: Affine<G0>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        pk_T: Affine<G1>,
        pk_T_gen: Affine<G1>,
        pk_T_gen_tables: &[Lookup3Bit<2, F0>],
        leaf_level_pc_gens: &PedersenGens<Affine<G0>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G0>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(REG_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            asset_id,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk,
            ID_LABEL,
            id,
            PK_T_LABEL,
            pk_T,
            PK_T_GEN_LABEL,
            pk_T_gen
        );

        // D = pk + g_k * asset_id + g_l * id
        let D = pk.into_group()
            + (account_comm_key.asset_id_gen() * F0::from(asset_id))
            + (account_comm_key.id_gen() * id);

        let reduced_acc_comm =
            (account_commitment.0.into_group() - D - initial_nullifier.into_group()).into_affine();
        self.resp_comm.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;

        self.resp_initial_nullifier.challenge_contribution(
            &account_comm_key.rho_gen(),
            &initial_nullifier,
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

        self.resp_comm
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
                &initial_nullifier,
                &account_comm_key.rho_gen(),
                &verifier_challenge,
            )
            .map_err(|_| {
                Error::ProofVerificationError("Initial nullifier verification failed".to_string())
            })?;

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
        let var_rho_sq = vars.pop().unwrap();
        let var_y_2 = vars.pop().unwrap();
        let var_x_2 = vars.pop().unwrap();
        let var_y_1 = vars.pop().unwrap();
        let var_x_1 = vars.pop().unwrap();

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
*/

fn ensure_correct_sk<G: AffineRepr>(
    account: &AccountState<G>,
    sk: G::ScalarField,
    sk_enc: G::ScalarField,
    aff_key_gen: G,
    enc_key_gen: G,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if account.pk_aff() != (aff_key_gen * sk).into_affine() {
            return Err(Error::RegistrationError(
                "Incorrect affirmation secret key".to_string(),
            ));
        }
        if account.pk_enc() != (enc_key_gen * sk_enc).into_affine() {
            return Err(Error::RegistrationError(
                "Incorrect encryption secret key".to_string(),
            ));
        }
        Ok(())
    }
}

fn ensure_correct_registration_state<G: AffineRepr>(account: &AccountState<G>) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if account.rho.square() != account.current_rho {
            return Err(Error::RegistrationError(
                "Rho relation not satisfied".to_string(),
            ));
        }
        if account.randomness.square() != account.current_randomness {
            return Err(Error::RegistrationError(
                "Randomness relation not satisfied".to_string(),
            ));
        }
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

// TODO: Check if "lazy_static" or equivalent no_std compatible
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

const SEPARATOR: &[u8; 2] = b"//";

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct MasterSeed(Vec<u8>);

impl MasterSeed {
    pub fn new(seed: Vec<u8>) -> Self {
        Self(seed)
    }

    /// Doesn't include asset-id to allow accounts to share secret keys
    pub fn derive_keys<G: AffineRepr, D: FullDigest>(
        &self,
        path: &[u8],
        counter: SkGenCounter,
        j: G,
        g: G,
    ) -> ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)) {
        // For creating secret keys, use `seed//path//counter`
        let mut extended_seed = self.0.to_vec();
        extended_seed.extend(SEPARATOR);
        extended_seed.extend_from_slice(path);
        extended_seed.extend(SEPARATOR);
        extended_seed.extend(counter.to_le_bytes());

        let sig_sk = hash_to_field::<G::ScalarField, D>(b"Signing key", &extended_seed);
        let enc_sk = hash_to_field::<G::ScalarField, D>(b"Encryption key", &extended_seed);

        let (sk, vk) = keygen_sig_given_sk(sig_sk, j);
        let (dk, ek) = keygen_enc_given_sk(enc_sk, g);

        extended_seed.zeroize();
        ((sk, vk), (dk, ek))
    }

    /// Returns `(randomness, rho_randomness)` where `randomness` is for the account commitment
    /// and `rho_randomness` is used to derive `rho`
    pub fn derive_account_randomness<G: AffineRepr, D: FullDigest>(
        &self,
        path: &[u8],
        counter_s: SkGenCounter,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> (G::ScalarField, G::ScalarField) {
        // For creating randomness, use `seed//path//counter_s//asset_id//counter_n`
        let mut extended_seed = self.0.to_vec();
        extended_seed.extend(SEPARATOR);
        extended_seed.extend_from_slice(path);
        extended_seed.extend(SEPARATOR);
        extended_seed.extend(counter_s.to_le_bytes());
        extended_seed.extend(SEPARATOR);
        extended_seed.extend(asset_id.to_le_bytes().as_slice());
        extended_seed.extend(SEPARATOR);
        extended_seed.extend(counter.to_le_bytes());
        // Need two independent field elements, `randomness`, `rho_randomness`
        let hasher = <DefaultFieldHasher<D> as HashToField<G::ScalarField>>::new(
            b"commitment and rho randomness",
        );
        let [randomness, rho_randomness]: [G::ScalarField; 2] =
            hasher.hash_to_field(&extended_seed);
        extended_seed.zeroize();
        (randomness, rho_randomness)
    }
}

#[cfg(test)]
pub mod tests {
    #![allow(deprecated)]

    use super::*;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::poseidon_impls::poseidon_2::Poseidon_hash_2_simple;
    use crate::poseidon_impls::poseidon_2::params::Poseidon2Params;
    use crate::poseidon_impls::poseidon_2::params::pallas::get_poseidon2_params_for_2_1_hashing;
    // use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
    // use ark_crypto_primitives::crh::{TwoToOneCRHScheme, TwoToOneCRHSchemeGadget};
    // use ark_crypto_primitives::{
    //     crh::poseidon::{TwoToOneCRH, constraints::TwoToOneCRHGadget},
    //     sponge::poseidon::PoseidonConfig,
    // };
    use ark_ff::Field;
    // use ark_r1cs_std::alloc::AllocVar;
    // use ark_r1cs_std::{
    //     R1CSVar,
    //     fields::fp::{AllocatedFp, FpVar},
    // };
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use bulletproofs::r1cs::{add_verification_tuples_to_rmc, batch_verify};
    use curve_tree_relations::parameters::SelRerandProofParameters;
    use polymesh_dart_common::AssetId;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type Fr = ark_pallas::Fr;

    /*pub fn test_params_for_poseidon_0<R: CryptoRngCore, F: PrimeField>(
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
    }*/

    pub fn test_params_for_poseidon2() -> Poseidon2Params<Fr> {
        get_poseidon2_params_for_2_1_hashing().unwrap()
    }

    /*#[test]
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
    }*/

    pub fn setup_comm_key(label: &[u8]) -> impl AccountCommitmentKeyTrait<PallasA> {
        [
            hash_to_pallas(label, b"sk-gen").into_affine(),
            hash_to_pallas(label, b"balance-gen").into_affine(),
            hash_to_pallas(label, b"counter-gen").into_affine(),
            hash_to_pallas(label, b"asset-id-gen").into_affine(),
            hash_to_pallas(label, b"rho-gen").into_affine(),
            hash_to_pallas(label, b"current-rho-gen").into_affine(),
            hash_to_pallas(label, b"randomness-gen").into_affine(),
            hash_to_pallas(label, b"current-randomness-gen").into_affine(),
            hash_to_pallas(label, b"id-gen").into_affine(),
            hash_to_pallas(label, b"sk-enc-inv-gen").into_affine(),
        ]
    }

    // pub fn new_account<R: CryptoRngCore, G: AffineRepr>(rng: &mut R, asset_id: AssetId, sk: SigKey<G>) -> (AccountState<G>, NullifierSkGenCounter, PoseidonConfig<G::ScalarField>) where G::ScalarField: Absorb {
    pub fn new_account<R: CryptoRngCore>(
        rng: &mut R,
        asset_id: AssetId,
        pk_aff: VerKey<PallasA>,
        pk_enc: EncKey<PallasA>,
        id: Fr,
    ) -> (
        AccountState<PallasA>,
        Fr,
        NullifierSkGenCounter,
        Poseidon2Params<Fr>,
    ) {
        let params = test_params_for_poseidon2();
        let counter = 1;
        let (account, rho_randomness) = AccountState::new(
            rng,
            id,
            pk_aff.0,
            pk_enc.0,
            asset_id,
            counter,
            params.clone(),
        )
        .unwrap();
        (account, rho_randomness, counter, params)
    }

    #[test]
    fn account_init() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;

        // Issuer creates keys
        let (_sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (_sk_enc, pk_enc) = keygen_enc(&mut rng, account_comm_key.sk_enc_gen());

        // User hashes it id onto the field
        let id = Fr::rand(&mut rng);

        let (mut account, rho_randomness, c, poseidon_config) =
            new_account(&mut rng, asset_id, pk_i, pk_enc.clone(), id);
        assert_eq!(account.id, id);
        assert_eq!(account.asset_id, asset_id);
        assert_eq!(account.balance, 0);
        assert_eq!(account.counter, 0);

        let combined = AccountState::<PallasA>::concat_asset_id_counter(asset_id, c);
        let expected_rho =
            Poseidon_hash_2_simple::<Fr>(rho_randomness, combined, poseidon_config).unwrap();
        assert_eq!(account.rho, expected_rho);
        assert_eq!(account.current_rho, account.rho.square());

        account.commit(account_comm_key).unwrap();

        let initial_rho = account.rho;
        let initial_randomness = account.randomness;
        assert_eq!(account.current_randomness, initial_randomness.square());

        // Test current_rho and current_randomness change correctly
        // After i iterations: current_rho = rho^{2+i} and current_randomness = initial_randomness^{2+i}
        // randomness (base s) remains constant
        let n = 10;
        for i in 1..=n {
            account.refresh_randomness_for_state_change();

            let expected_current_rho = initial_rho.pow([2 + i as u64]);

            let expected_current_randomness = initial_randomness.pow([2 + i as u64]);

            assert_eq!(account.current_rho, expected_current_rho);
            assert_eq!(account.randomness, initial_randomness); // base s stays constant
            assert_eq!(account.current_randomness, expected_current_randomness);
        }
    }

    #[test]
    fn test_deterministic_key_and_randomness_generation() {
        let mut rng = rand::thread_rng();

        let id = Fr::rand(&mut rng);
        let asset_id = 1;
        let counter_s = 1;
        let counter_n = 1;

        let seed1 = MasterSeed::new(b"test_seed".to_vec());

        let seed2 = MasterSeed::new(b"different_seed".to_vec());

        let j = PallasA::rand(&mut rng);
        let g = PallasA::rand(&mut rng);

        let params = test_params_for_poseidon2();

        let result1 = seed1.derive_keys::<PallasA, Blake2b512>(b"path", counter_s, j, g);
        let result2 = seed1.derive_keys::<PallasA, Blake2b512>(b"path", counter_s, j, g);
        assert_eq!(result1, result2);

        // Same seed, different path
        let result3 = seed1.derive_keys::<PallasA, Blake2b512>(b"path1", counter_s, j, g);
        assert_ne!(result1, result3);

        // Same seed, same path, different counter
        let result4 = seed1.derive_keys::<PallasA, Blake2b512>(b"path", counter_s + 1, j, g);
        assert_ne!(result1, result4);

        // Different seed, same path and counter
        let result5 = seed2.derive_keys::<PallasA, Blake2b512>(b"path", counter_s, j, g);
        assert_ne!(result1, result5);

        // Returns (randomness, rho_randomness) tuple
        let rand1 = seed1.derive_account_randomness::<PallasA, Blake2b512>(
            b"path", counter_s, asset_id, counter_n,
        );
        let rand2 = seed1.derive_account_randomness::<PallasA, Blake2b512>(
            b"path", counter_s, asset_id, counter_n,
        );
        assert_eq!(rand1, rand2);

        // Different counter
        let rand3 = seed2.derive_account_randomness::<PallasA, Blake2b512>(
            b"path",
            counter_s,
            asset_id,
            counter_n + 1,
        );
        assert_ne!(rand1, rand3);

        let rand4 = seed2.derive_account_randomness::<PallasA, Blake2b512>(
            b"path",
            counter_s + 1,
            asset_id,
            counter_n,
        );
        assert_ne!(rand1, rand4);

        let rand5 = seed1.derive_account_randomness::<PallasA, Blake2b512>(
            b"path1", counter_s, asset_id, counter_n,
        );
        assert_ne!(rand1, rand5);

        let pk1 = result1.0.1.0;
        let pk1_enc = result1.1.1.0;
        let pk2 = result3.0.1.0;
        let pk2_enc = result3.1.1.0;

        let account1 = AccountState::<PallasA>::new_given_randomness(
            id,
            pk1,
            pk1_enc,
            asset_id,
            counter_n,
            rand1.0,
            rand1.1,
            params.clone(),
        )
        .unwrap();
        let account2 = AccountState::<PallasA>::new_given_randomness(
            id,
            pk1,
            pk1_enc,
            asset_id,
            counter_n,
            rand2.0,
            rand2.1,
            params.clone(),
        )
        .unwrap();
        assert_eq!(account1, account2);

        // Different randomness
        let account3 = AccountState::<PallasA>::new_given_randomness(
            id,
            pk1,
            pk1_enc,
            asset_id,
            counter_n,
            rand3.0,
            rand3.1,
            params.clone(),
        )
        .unwrap();
        assert_ne!(account1, account3);

        // Same randomness, different sk
        let account4 = AccountState::<PallasA>::new_given_randomness(
            id,
            pk2,
            pk2_enc,
            asset_id,
            counter_n,
            rand1.0,
            rand1.1,
            params.clone(),
        )
        .unwrap();
        assert_ne!(account1, account4);
    }

    #[test]
    fn registration_without_pk_T() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;

        // Investor creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);

        let clock = Instant::now();
        let (account, rho_randomness, nullifier_gen_counter, poseidon_params) =
            new_account(&mut rng, asset_id, pk_i, pk_enc, id.clone());
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce-0";

        let reg_proof = RegTxnProof::<_, 48, 6>::new(
            &mut rng,
            sk_i.0,
            sk_enc.0,
            &account,
            account_comm.clone(),
            rho_randomness,
            nullifier_gen_counter,
            nonce,
            account_comm_key.clone(),
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &poseidon_params,
            None,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        // Verify without RandomizedMultChecker
        let clock = Instant::now();
        reg_proof
            .verify(
                &mut rng,
                id,
                pk_i.0,
                pk_enc.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key.clone(),
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                None,
                None,
            )
            .unwrap();

        let verifier_time_regular = clock.elapsed();

        let clock = Instant::now();
        let mut rmc = RandomizedMultChecker::new(Fr::rand(&mut rng));
        reg_proof
            .verify(
                &mut rng,
                id,
                pk_i.0,
                pk_enc.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key,
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                None,
                Some(&mut rmc),
            )
            .unwrap();
        rmc.verify().unwrap();
        let verifier_time_rmc = clock.elapsed();

        println!("For reg. txn");
        println!("total proof size = {}", reg_proof.compressed_size());
        println!("total prover time = {:?}", prover_time);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular, verifier_time_rmc
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
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;

        // Investor creates keys
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let enc_gen = PallasA::rand(&mut rng);
        let (sk_T, pk_T) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);

        let clock = Instant::now();
        let (mut account, rho_randomness, nullifier_gen_counter, poseidon_params) =
            new_account(&mut rng, asset_id, pk, pk_enc, id.clone());
        // Make randomness small to run test faster
        account.randomness = Fr::from(u16::rand(&mut rng) as u64 + u8::rand(&mut rng) as u64);
        // current_randomness = randomness^2 (same relation as current_rho = rho^2)
        account.current_randomness = account.randomness.square();
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce-0";

        let reg_proof = RegTxnProof::<_, CHUNK_BITS, NUM_CHUNKS>::new(
            &mut rng,
            sk.0,
            sk_enc.0,
            &account,
            account_comm.clone(),
            rho_randomness,
            nullifier_gen_counter,
            nonce,
            account_comm_key.clone(),
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &poseidon_params,
            Some((pk_T.0, enc_key_gen, enc_gen)),
        )
        .unwrap();

        let prover_time = clock.elapsed();

        // Verify without RandomizedMultChecker
        let clock = Instant::now();
        reg_proof
            .verify(
                &mut rng,
                id,
                pk.0,
                pk_enc.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key.clone(),
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                Some((pk_T.0, enc_key_gen, enc_gen)),
                None,
            )
            .unwrap();

        let verifier_time_regular = clock.elapsed();

        // Verify with RandomizedMultChecker
        let mut rmc = RandomizedMultChecker::new(Fr::rand(&mut rng));
        let clock = Instant::now();
        reg_proof
            .verify(
                &mut rng,
                id,
                pk.0,
                pk_enc.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                account_comm_key,
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                Some((pk_T.0, enc_key_gen, enc_gen)),
                Some(&mut rmc),
            )
            .unwrap();
        rmc.verify().unwrap();
        let verifier_time_rmc = clock.elapsed();

        println!("For reg. txn with {NUM_CHUNKS} chunks each of {CHUNK_BITS} bits");
        println!("total proof size = {}", reg_proof.compressed_size());
        println!(
            "ciphertext and its proof size = {}",
            reg_proof
                .partial
                .encryption_for_T
                .as_ref()
                .unwrap()
                .encrypted_randomness
                .compressed_size()
        );
        println!("total prover time = {:?}", prover_time);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular, verifier_time_rmc
        );

        // This will take a long time to decrypt
        let clock = Instant::now();
        assert_eq!(
            account.randomness,
            reg_proof
                .partial
                .encryption_for_T
                .unwrap()
                .encrypted_randomness
                .decrypt(&sk_T.0, enc_gen.into_group())
                .unwrap()
        );
        println!("decryption time = {:?}", clock.elapsed());
    }

    #[test]
    fn registration_parallel_workflow() {
        // W2 (Parallel): Host and Ledger each build their own independent transcript.
        // Host derives challenge_h from REG_TXN_LABEL transcript + partial T-values (no auth).
        // Ledger derives challenge_l from its own AUTH_TXN_LABEL transcript with nonce only.
        // Verifier replicates each side's transcript independently.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 12;
        let account_tree_params =
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();
        let account_comm_key = setup_comm_key(b"testing");
        let asset_id = 1;
        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);
        let enc_key_gen = account_comm_key.sk_enc_gen();
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let (account, rho_randomness, nullifier_gen_counter, poseidon_params) =
            new_account(&mut rng, asset_id, pk_aff, pk_enc, id.clone());
        let account_comm = account.commit(account_comm_key.clone()).unwrap();
        let nonce = b"test-nonce-0";

        let leaf_level_pc_gens = account_tree_params.even_parameters.pc_gens();
        let leaf_level_bp_gens = account_tree_params.even_parameters.bp_gens();

        let aff_key_gen = account_comm_key.sk_gen();

        //  Host side: own REG_TXN_LABEL transcript, public inputs + partial T-values
        let partial = RegTxnWithoutSkProtocol::<_, 48, 6>::new(
            &mut rng,
            pk_aff.0,
            pk_enc.0,
            &account,
            account_comm.clone(),
            rho_randomness,
            nullifier_gen_counter,
            nonce,
            &account_comm_key,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            &poseidon_params,
            None,
        )
        .unwrap();

        //  Ledger side: own AUTH_TXN_LABEL transcript, independently
        let auth_proof = AuthProofOnlySks::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            pk_aff.0,
            pk_enc.0,
            nonce,
            &aff_key_gen,
            &enc_key_gen,
        )
        .unwrap();

        let reg_proof = RegTxnProof::<_, 48, 6> {
            auth_proof,
            partial,
        };

        //  verify each side with its own independent challenge
        let mut verifier = reg_proof
            .partial
            .challenge_contribution(
                id,
                pk_aff.0,
                pk_enc.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                &account_comm_key,
                &poseidon_params,
                None,
            )
            .unwrap();

        // Verifier derives partial challenge from its own transcript (no auth T-values)
        let challenge_h_v = verifier
            .transcript()
            .challenge_scalar::<Fr>(TXN_CHALLENGE_LABEL);

        reg_proof
            .partial
            .verify_with_challenge(
                &challenge_h_v,
                &account_comm_key,
                pk_aff.0,
                pk_enc.0,
                id,
                asset_id,
                &account_comm,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                None,
                None,
            )
            .unwrap();

        // Verify auth proof using its own AUTH_TXN_LABEL transcript
        reg_proof
            .auth_proof
            .verify(pk_aff.0, pk_enc.0, nonce, &aff_key_gen, &enc_key_gen, None)
            .unwrap();

        let proof = reg_proof.partial.proof.as_ref().unwrap();
        let tuple = verifier
            .verification_scalars_and_points_with_rng(proof, &mut rng)
            .unwrap();
        verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens).unwrap();
    }

    #[test]
    fn registration_sequential_workflow() {
        // W3 (Sequential): Host derives partial challenge first, sends it to Ledger.
        // Ledger uses ledger_nonce = [challenge_h_bytes || original_nonce] for its own AUTH_TXN_LABEL transcript.
        // Verifier replicates: derive partial challenge, verify partial, recompute ledger nonce, verify auth.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 12;
        let account_tree_params =
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();
        let account_comm_key = setup_comm_key(b"testing");
        let asset_id = 1;
        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);
        let enc_key_gen = account_comm_key.sk_enc_gen();
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let (account, rho_randomness, nullifier_gen_counter, poseidon_params) =
            new_account(&mut rng, asset_id, pk_aff, pk_enc, id.clone());
        let account_comm = account.commit(account_comm_key.clone()).unwrap();
        let nonce = b"test-nonce-0";

        let leaf_level_pc_gens = account_tree_params.even_parameters.pc_gens();
        let leaf_level_bp_gens = account_tree_params.even_parameters.bp_gens();

        let aff_key_gen = account_comm_key.sk_gen();

        //  Host pre-challenge phase
        let (protocol, mut prover) = RegTxnWithoutSkProtocol::<_, 48, 6>::init(
            &mut rng,
            pk_aff.0,
            pk_enc.0,
            &account,
            account_comm.clone(),
            rho_randomness,
            nullifier_gen_counter,
            nonce,
            &account_comm_key,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            &poseidon_params,
            None,
        )
        .unwrap();

        let challenge_h = prover
            .transcript()
            .challenge_scalar::<Fr>(TXN_CHALLENGE_LABEL);

        //  Host sends challenge_h bytes to Ledger
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        let auth_proof = AuthProofOnlySks::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            pk_aff.0,
            pk_enc.0,
            &ledger_nonce,
            &aff_key_gen,
            &enc_key_gen,
        )
        .unwrap();

        //  Host hashes auth_proof into the transcript to derive an updated challenge
        let mut auth_proof_bytes = Vec::new();
        auth_proof
            .serialize_compressed(&mut auth_proof_bytes)
            .unwrap();
        prover
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes);
        let challenge_h_final = prover
            .transcript()
            .challenge_scalar::<Fr>(TXN_CHALLENGE_LABEL);

        //  Host post-challenge phase, host could create a new challenge by hashing the ledger proof into challenge_h
        let mut partial = protocol.gen_proof(&challenge_h_final).unwrap();
        let r1cs_proof = prover
            .prove_with_rng(&leaf_level_bp_gens, &mut rng)
            .unwrap();
        partial.proof = Some(r1cs_proof);

        let reg_proof = RegTxnProof::<_, 48, 6> {
            auth_proof,
            partial,
        };

        //  derive partial challenge, verify partial, recompute ledger nonce, verify auth
        let mut verifier = reg_proof
            .partial
            .challenge_contribution(
                id,
                pk_aff.0,
                pk_enc.0,
                asset_id,
                &account_comm,
                nullifier_gen_counter,
                nonce,
                &account_comm_key,
                &poseidon_params,
                None,
            )
            .unwrap();

        let challenge_h_v = verifier
            .transcript()
            .challenge_scalar::<Fr>(TXN_CHALLENGE_LABEL);

        // Verifier recomputes ledger nonce from the partial challenge
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        reg_proof
            .auth_proof
            .verify(
                pk_aff.0,
                pk_enc.0,
                &ledger_nonce_v,
                &aff_key_gen,
                &enc_key_gen,
                None,
            )
            .unwrap();

        // Verifier hashes auth_proof into the transcript to derive the updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        reg_proof
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        verifier
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = verifier
            .transcript()
            .challenge_scalar::<Fr>(TXN_CHALLENGE_LABEL);

        reg_proof
            .partial
            .verify_with_challenge(
                &challenge_h_final_v,
                &account_comm_key,
                pk_aff.0,
                pk_enc.0,
                id,
                asset_id,
                &account_comm,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                None,
                None,
            )
            .unwrap();

        let proof = reg_proof.partial.proof.as_ref().unwrap();
        let tuple = verifier
            .verification_scalars_and_points_with_rng(proof, &mut rng)
            .unwrap();
        verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens).unwrap();
    }

    /*
    #[test]
    fn registration_alt() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

        let account_comm_key = setup_comm_key(b"testing");

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

        let (reg_proof, nullifier) = RegTxnProofAlt::new(
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
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
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
                nullifier,
                nonce,
                account_comm_key,
                pk_T.0,
                enc_key_gen,
                &tables,
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
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
            (reg_proof.T_1 * sk_inv).into_affine().x().unwrap(),
            account.rho
        );
        assert_eq!(
            (reg_proof.T_2 * sk_inv).into_affine().x().unwrap(),
            account.randomness
        );
    }
    */

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
        rho_randomness: Fr,
        rho: Fr,
        randomness: Fr,
        current_randomness: Fr,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        poseidon_params: &Poseidon2Params<Fr>,
    ) -> bool {
        let values = vec![
            rho_randomness,
            rho,
            rho.square(),
            randomness,
            current_randomness,
        ];

        let prover_transcript = MerlinTranscript::new(b"test");
        let mut prover = Prover::new(pc_gens, prover_transcript);
        let (comm, vars) = prover.commit_vec(&values, Fr::from(200u64), bp_gens);

        if RegTxnWithoutSkProof::<PallasA, 48, 6>::enforce_constraints(
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
        let vars = verifier.commit_vec(5, comm);

        if RegTxnWithoutSkProof::<PallasA, 48, 6>::enforce_constraints(
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

        let rho_randomness = Fr::rand(&mut rng);
        let asset_id = 2;
        let counter = 1;

        let poseidon_params = test_params_for_poseidon2();
        let combined = AccountState::<PallasA>::concat_asset_id_counter(asset_id, counter);
        let rho = Poseidon_hash_2_simple::<Fr>(rho_randomness, combined, poseidon_params.clone())
            .unwrap();

        let randomness = Fr::rand(&mut rng);
        let current_randomness = randomness.square();

        // Correct inputs: proof must verify
        assert!(prove_verify_rho_gen_constraints(
            &pc_gens,
            &bp_gens,
            rho_randomness,
            rho,
            randomness,
            current_randomness,
            asset_id,
            counter,
            &poseidon_params
        ));

        // Wrong rho (Poseidon pre-image fails): proof must not verify
        let wrong_rho = Fr::rand(&mut rng);
        assert!(!prove_verify_rho_gen_constraints(
            &pc_gens,
            &bp_gens,
            rho_randomness,
            wrong_rho,
            randomness,
            current_randomness,
            asset_id,
            counter,
            &poseidon_params
        ));

        // Wrong current_randomness (square relation breaks): proof must not verify
        let wrong_current_randomness = Fr::rand(&mut rng);
        assert!(!prove_verify_rho_gen_constraints(
            &pc_gens,
            &bp_gens,
            rho_randomness,
            rho,
            randomness,
            wrong_current_randomness,
            asset_id,
            counter,
            &poseidon_params
        ));
    }

    #[test]
    fn batch_registration() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

        const CHUNK_BITS: usize = 48;
        const NUM_CHUNKS: usize = 6;

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

        let account_comm_key = setup_comm_key(b"testing");

        let poseidon_params = test_params_for_poseidon2();
        let nullifier_gen_counter = 1;

        let batch_size = 5_usize;

        let asset_ids = (0..batch_size)
            .map(|i| (i + 1) as u32)
            .collect::<Vec<AssetId>>();
        // Create unique nonces for each proof
        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("test_nonce_{}", i).into_bytes())
            .collect();

        // Create multiple proofs
        let mut proofs_without_pk_T = Vec::new();
        let mut proofs_with_pk_T = Vec::new();
        let mut ids = Vec::new();
        let mut sks = Vec::new();
        let mut sk_encs = Vec::new();
        let mut pks = Vec::new();
        let mut pk_encs = Vec::new();
        let mut accounts = Vec::new();
        let mut account_comms = Vec::new();
        let mut rho_randomnesses = Vec::new();

        for i in 0..batch_size {
            // Create unique keys and account for each proof
            let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let id = Fr::rand(&mut rng);
            let (sk_enc, pk_enc) = keygen_enc(&mut rng, account_comm_key.sk_enc_gen());

            let (account, rho_randomness) = AccountState::new(
                &mut rng,
                id,
                pk_i.0,
                pk_enc.0,
                asset_ids[i],
                nullifier_gen_counter,
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
        }

        for i in 0..batch_size {
            let reg_proof = RegTxnProof::<_, CHUNK_BITS, NUM_CHUNKS>::new(
                &mut rng,
                sks[i],
                sk_encs[i],
                &accounts[i],
                account_comms[i],
                rho_randomnesses[i],
                nullifier_gen_counter,
                nonces[i].as_slice(),
                account_comm_key.clone(),
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                None,
            )
            .unwrap();

            proofs_without_pk_T.push(reg_proof);
        }

        let clock = Instant::now();

        for i in 0..batch_size {
            proofs_without_pk_T[i]
                .verify(
                    &mut rng,
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    None,
                    None,
                )
                .unwrap();
        }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut tuples = Vec::new();

        // Can be done in parallel
        for i in 0..batch_size {
            let tuple = proofs_without_pk_T[i]
                .verify_and_return_tuples(
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    None,
                    &mut rng,
                    None,
                )
                .unwrap();

            tuples.push(tuple);
        }

        batch_verify(
            tuples,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
        )
        .unwrap();

        let batch_verifier_time = clock.elapsed();

        println!(
            "For {batch_size} proofs without pk_T, verifier time = {:?}, batch verifier time {:?} and proof size {}",
            verifier_time,
            batch_verifier_time,
            proofs_without_pk_T.compressed_size()
        );

        // Now create proofs with pk_T
        let enc_key_gen_with_pk_T = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);
        let (_, pk_T) = keygen_enc(&mut rng, enc_key_gen_with_pk_T);

        for i in 0..batch_size {
            let reg_proof = RegTxnProof::<_, CHUNK_BITS, NUM_CHUNKS>::new(
                &mut rng,
                sks[i],
                sk_encs[i],
                &accounts[i],
                account_comms[i],
                rho_randomnesses[i],
                nullifier_gen_counter,
                nonces[i].as_slice(),
                account_comm_key.clone(),
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                Some((pk_T.0, enc_key_gen_with_pk_T, enc_gen)),
            )
            .unwrap();

            proofs_with_pk_T.push(reg_proof);
        }

        let clock = Instant::now();

        for i in 0..batch_size {
            proofs_with_pk_T[i]
                .verify(
                    &mut rng,
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    Some((pk_T.0, enc_key_gen_with_pk_T, enc_gen)),
                    None,
                )
                .unwrap();
        }

        let verifier_time_with_pk_T = clock.elapsed();

        let clock = Instant::now();

        let mut tuples_with_pk_T = Vec::new();

        // Can be done in parallel
        for i in 0..batch_size {
            let tuple = proofs_with_pk_T[i]
                .verify_and_return_tuples(
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &&poseidon_params,
                    Some((pk_T.0, enc_key_gen_with_pk_T, enc_gen)),
                    &mut rng,
                    None,
                )
                .unwrap();

            tuples_with_pk_T.push(tuple);
        }

        batch_verify(
            tuples_with_pk_T,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
        )
        .unwrap();

        let batch_verifier_time_with_pk_T = clock.elapsed();

        println!(
            "For {batch_size} proofs with pk_T, verifier time = {:?}, batch verifier time {:?} and proof size {}",
            verifier_time_with_pk_T,
            batch_verifier_time_with_pk_T,
            proofs_with_pk_T.compressed_size()
        );

        // Test batch verification with RandomizedMultChecker for proofs without pk_T
        let clock = Instant::now();

        let mut rmc = RandomizedMultChecker::new(Fr::rand(&mut rng));
        let mut tuples = vec![];
        // These can also be done in parallel
        for i in 0..batch_size {
            tuples.push(
                proofs_without_pk_T[i]
                    .verify_and_return_tuples(
                        ids[i],
                        pks[i],
                        pk_encs[i],
                        asset_ids[i],
                        &account_comms[i],
                        nullifier_gen_counter,
                        &nonces[i],
                        account_comm_key.clone(),
                        &account_tree_params.even_parameters.pc_gens(),
                        &account_tree_params.even_parameters.bp_gens(),
                        &poseidon_params,
                        None,
                        &mut rng,
                        Some(&mut rmc),
                    )
                    .unwrap(),
            );
        }

        add_verification_tuples_to_rmc(
            tuples,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &mut rmc,
        )
        .unwrap();
        rmc.verify().unwrap();
        let rmc_verifier_time = clock.elapsed();

        // Test batch verification with RandomizedMultChecker for proofs with pk_T
        let clock = Instant::now();

        let mut rmc_with_pk_T = RandomizedMultChecker::new(Fr::rand(&mut rng));
        let mut tuples = vec![];

        // These can also be done in parallel
        for i in 0..batch_size {
            tuples.push(
                proofs_with_pk_T[i]
                    .verify_and_return_tuples(
                        ids[i],
                        pks[i],
                        pk_encs[i],
                        asset_ids[i],
                        &account_comms[i],
                        nullifier_gen_counter,
                        &nonces[i],
                        account_comm_key.clone(),
                        &account_tree_params.even_parameters.pc_gens(),
                        &account_tree_params.even_parameters.bp_gens(),
                        &poseidon_params,
                        Some((pk_T.0, enc_key_gen_with_pk_T, enc_gen)),
                        &mut rng,
                        Some(&mut rmc_with_pk_T),
                    )
                    .unwrap(),
            );
        }

        add_verification_tuples_to_rmc(
            tuples,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &mut rmc_with_pk_T,
        )
        .unwrap();
        rmc_with_pk_T.verify().unwrap();
        let rmc_verifier_time_with_pk_T = clock.elapsed();

        println!(
            "For {batch_size} proofs without pk_T, RandomizedMultChecker verifier time = {:?}",
            rmc_verifier_time
        );
        println!(
            "For {batch_size} proofs with pk_T, RandomizedMultChecker verifier time = {:?}",
            rmc_verifier_time_with_pk_T
        );
    }

    #[test]
    fn combined_registration() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

        let account_comm_key = setup_comm_key(b"testing");

        let poseidon_params = test_params_for_poseidon2();
        let nullifier_gen_counter = 1;

        let batch_size = 5;
        let asset_ids = (0..batch_size)
            .map(|i| (i + 1) as AssetId)
            .collect::<Vec<AssetId>>();
        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("test_nonce_{}", i).into_bytes())
            .collect();

        let mut ids = vec![];
        let mut sks = vec![];
        let mut sk_encs = vec![];
        let mut pks = vec![];
        let mut pk_encs = vec![];
        let mut accounts = vec![];
        let mut account_comms = vec![];
        let mut rho_randomnesses = vec![];

        let enc_key_gen = account_comm_key.sk_enc_gen();

        // Create accounts
        for i in 0..batch_size {
            // Create unique keys and account for each proof
            let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let id = Fr::rand(&mut rng);
            ids.push(id);
            let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);

            let (account, rho_randomness) = AccountState::new(
                &mut rng,
                id,
                pk_i.0,
                pk_enc.0,
                asset_ids[i],
                nullifier_gen_counter,
                poseidon_params.clone(),
            )
            .unwrap();
            accounts.push(account);
            rho_randomnesses.push(rho_randomness);

            let account_comm = accounts[i].commit(account_comm_key.clone()).unwrap();
            account_comms.push(account_comm);

            sks.push(sk_i.0);
            sk_encs.push(sk_enc.0);
            pks.push(pk_i.0);
            pk_encs.push(pk_enc.0);
        }

        // Combined proving without pk_T
        let clock = Instant::now();
        let transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut prover = Prover::new(&account_tree_params.even_parameters.pc_gens(), transcript);
        let mut proofs_without_pk_T = vec![];
        for i in 0..batch_size {
            let proof = RegTxnProof::<_, 48, 6>::new_with_given_prover(
                &mut rng,
                sks[i],
                sk_encs[i],
                &accounts[i],
                account_comms[i].clone(),
                rho_randomnesses[i],
                nullifier_gen_counter,
                &nonces[i],
                account_comm_key.clone(),
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                None,
                &mut prover,
            )
            .unwrap();
            proofs_without_pk_T.push(proof);
        }

        let r1cs_proof_without_pk_T = prover
            .prove_with_rng(&account_tree_params.even_parameters.bp_gens(), &mut rng)
            .unwrap();

        let proving_time_without_pk_T = clock.elapsed();

        let clock = Instant::now();
        let verifier_transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);

        for i in 0..batch_size {
            proofs_without_pk_T[i]
                .verify_sigma_protocols_and_enforce_constraints(
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    None,
                    &mut verifier,
                    None,
                )
                .unwrap();
        }

        let tuple_without_pk_T = verifier
            .verification_scalars_and_points_with_rng(&r1cs_proof_without_pk_T, &mut rng)
            .unwrap();

        // Verify the tuple
        verify_given_verification_tuple(
            tuple_without_pk_T,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
        )
        .unwrap();

        let verification_time_without_pk_T = clock.elapsed();

        // Combined verification with RandomizedMultChecker without pk_T
        let clock = Instant::now();
        let mut rmc_without_pk_T = RandomizedMultChecker::new(Fr::rand(&mut rng));
        let verifier_transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);

        for i in 0..batch_size {
            proofs_without_pk_T[i]
                .verify_sigma_protocols_and_enforce_constraints(
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    None,
                    &mut verifier,
                    Some(&mut rmc_without_pk_T),
                )
                .unwrap();
        }

        let tuple_rmc_without_pk_T = verifier
            .verification_scalars_and_points_with_rng(&r1cs_proof_without_pk_T, &mut rng)
            .unwrap();

        add_verification_tuples_to_rmc(
            vec![tuple_rmc_without_pk_T],
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &mut rmc_without_pk_T,
        )
        .unwrap();
        rmc_without_pk_T.verify().unwrap();
        let rmc_verification_time_without_pk_T = clock.elapsed();

        // Now create proofs with pk_T
        let enc_key_gen_with_pk_T = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);
        let (_, pk_T) = keygen_enc(&mut rng, enc_key_gen_with_pk_T);

        let clock = Instant::now();
        let transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut prover = Prover::new(&account_tree_params.even_parameters.pc_gens(), transcript);

        let mut proofs_with_pk_T = vec![];
        for i in 0..batch_size {
            let proof = RegTxnProof::<_, 48, 6>::new_with_given_prover(
                &mut rng,
                sks[i],
                sk_encs[i],
                &accounts[i],
                account_comms[i].clone(),
                rho_randomnesses[i],
                nullifier_gen_counter,
                &nonces[i],
                account_comm_key.clone(),
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                Some((pk_T.0, enc_key_gen_with_pk_T, enc_gen)),
                &mut prover,
            )
            .unwrap();
            proofs_with_pk_T.push(proof);
        }

        let r1cs_proof_with_pk_T = prover
            .prove_with_rng(&account_tree_params.even_parameters.bp_gens(), &mut rng)
            .unwrap();

        let proving_time_with_pk_T = clock.elapsed();

        let clock = Instant::now();
        let verifier_transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);

        for i in 0..batch_size {
            proofs_with_pk_T[i]
                .verify_sigma_protocols_and_enforce_constraints(
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    Some((pk_T.0, enc_key_gen_with_pk_T, enc_gen)),
                    &mut verifier,
                    None,
                )
                .unwrap();
        }

        let tuple_with_pk_T = verifier
            .verification_scalars_and_points_with_rng(&r1cs_proof_with_pk_T, &mut rng)
            .unwrap();

        // Verify the tuple
        verify_given_verification_tuple(
            tuple_with_pk_T,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
        )
        .unwrap();

        let verification_time_with_pk_T = clock.elapsed();

        // Combined verification with RandomizedMultChecker with pk_T
        let clock = Instant::now();
        let mut rmc_with_pk_T = RandomizedMultChecker::new(Fr::rand(&mut rng));
        let verifier_transcript = MerlinTranscript::new(REG_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);

        for i in 0..batch_size {
            proofs_with_pk_T[i]
                .verify_sigma_protocols_and_enforce_constraints(
                    ids[i],
                    pks[i],
                    pk_encs[i],
                    asset_ids[i],
                    &account_comms[i],
                    nullifier_gen_counter,
                    &nonces[i],
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    Some((pk_T.0, enc_key_gen_with_pk_T, enc_gen)),
                    &mut verifier,
                    Some(&mut rmc_with_pk_T),
                )
                .unwrap();
        }

        let tuple_rmc_with_pk_T = verifier
            .verification_scalars_and_points_with_rng(&r1cs_proof_with_pk_T, &mut rng)
            .unwrap();

        add_verification_tuples_to_rmc(
            vec![tuple_rmc_with_pk_T],
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &mut rmc_with_pk_T,
        )
        .unwrap();
        rmc_with_pk_T.verify().unwrap();
        let rmc_verification_time_with_pk_T = clock.elapsed();

        println!(
            "Combined registration proving time without pk_T = {:?}",
            proving_time_without_pk_T
        );
        println!(
            "Combined registration verification time without pk_T = {:?}",
            verification_time_without_pk_T
        );
        println!(
            "Combined registration RMC verification time without pk_T = {:?}",
            rmc_verification_time_without_pk_T
        );
        println!(
            "Combined proof size without pk_T = {} bytes",
            r1cs_proof_without_pk_T.compressed_size() + proofs_without_pk_T.compressed_size()
        );
        println!(
            "Combined registration proving time with pk_T = {:?}",
            proving_time_with_pk_T
        );
        println!(
            "Combined registration verification time with pk_T = {:?}",
            verification_time_with_pk_T
        );
        println!(
            "Combined registration RMC verification time with pk_T = {:?}",
            rmc_verification_time_with_pk_T
        );
        println!(
            "Combined proof size with pk_T = {} bytes",
            r1cs_proof_with_pk_T.compressed_size() + proofs_with_pk_T.compressed_size()
        );
    }

    // Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

    #[cfg(feature = "ignore_prover_input_sanitation")]
    mod input_sanitation_disabled {
        use super::*;

        #[test]
        fn registration_with_non_zero_balance() {
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)

            // Create public params (generators, etc)
            let account_tree_params =
                SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                    NUM_GENS as u32,
                    NUM_GENS as u32,
                )
                .unwrap();

            let account_comm_key = setup_comm_key(b"testing");

            let asset_id = 1;

            // Investor creates keys
            let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let id = Fr::rand(&mut rng);

            let enc_key_gen = account_comm_key.sk_enc_gen();
            let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);

            let (mut account, rho_randomness, nullifier_gen_counter, poseidon_params) =
                new_account(&mut rng, asset_id, sk_i, sk_enc, id.clone());

            // Set non-zero balance - this should cause proof verification to fail
            account.balance = 100;

            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            let nonce = b"test-nonce-0";

            let pk_enc = (enc_key_gen * account.sk_enc).into_affine();

            // With ignore_prover_input_sanitation, proof creation should succeed
            let reg_proof = RegTxnProof::<_, 48, 6>::new(
                &mut rng,
                pk_i.0,
                pk_enc,
                &account,
                account_comm.clone(),
                rho_randomness,
                nullifier_gen_counter,
                nonce,
                account_comm_key.clone(),
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
                &poseidon_params,
                None,
            )
            .unwrap();

            assert!(
                reg_proof
                    .verify(
                        &mut rng,
                        id,
                        pk_i.0,
                        pk_enc,
                        asset_id,
                        &account_comm,
                        nullifier_gen_counter,
                        nonce,
                        account_comm_key,
                        &account_tree_params.even_parameters.pc_gens(),
                        &account_tree_params.even_parameters.bp_gens(),
                        &poseidon_params,
                        None,
                        None,
                    )
                    .is_err()
            );
        }

        #[test]
        fn registration_with_incorrect_keys() {
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 12;

            let account_tree_params =
                SelRerandProofParameters::<PallasParameters, VestaParameters>::new(
                    NUM_GENS as u32,
                    NUM_GENS as u32,
                )
                .unwrap();

            let account_comm_key = setup_comm_key(b"testing");
            let enc_key_gen = account_comm_key.sk_enc_gen();

            let asset_id = 1;
            let id = Fr::rand(&mut rng);
            let nullifier_gen_counter = 1;
            let poseidon_params = test_params_for_poseidon2();

            // Wrong affirmation secret key in account state
            {
                let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
                let (sk_wrong, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
                let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);

                // Create account with wrong affirmation key
                let (account, rho_randomness) = AccountState::new(
                    &mut rng,
                    id,
                    sk_wrong.0,
                    sk_enc.0,
                    asset_id,
                    nullifier_gen_counter,
                    poseidon_params.clone(),
                )
                .unwrap();

                let account_comm = account.commit(account_comm_key.clone()).unwrap();
                let nonce = b"test-nonce-1";

                // Proof creation succeeds with ignore_prover_input_sanitation
                let reg_proof = RegTxnProof::<_, 48, 6>::new(
                    &mut rng,
                    pk_i.0,
                    pk_enc.0,
                    &account,
                    account_comm.clone(),
                    rho_randomness,
                    nullifier_gen_counter,
                    nonce,
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    None,
                )
                .unwrap();

                // Verification should fail because pk doesn't match account.sk
                assert!(
                    reg_proof
                        .verify(
                            &mut rng,
                            id,
                            pk_i.0,
                            pk_enc.0,
                            asset_id,
                            &account_comm,
                            nullifier_gen_counter,
                            nonce,
                            account_comm_key.clone(),
                            &account_tree_params.even_parameters.pc_gens(),
                            &account_tree_params.even_parameters.bp_gens(),
                            &poseidon_params,
                            None,
                            None,
                        )
                        .is_err()
                );
            }

            // Wrong encryption secret key in account state
            {
                let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
                let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
                let (sk_enc_wrong, _) = keygen_enc(&mut rng, enc_key_gen);

                // Create account with wrong encryption key inverse
                let (account, rho_randomness) = AccountState::new(
                    &mut rng,
                    id,
                    sk_i.0,
                    sk_enc_wrong.0,
                    asset_id,
                    nullifier_gen_counter,
                    poseidon_params.clone(),
                )
                .unwrap();

                let account_comm = account.commit(account_comm_key.clone()).unwrap();
                let nonce = b"test-nonce-2";

                // Proof creation succeeds with ignore_prover_input_sanitation
                let reg_proof = RegTxnProof::<_, 48, 6>::new(
                    &mut rng,
                    pk_i.0,
                    pk_enc.0,
                    &account,
                    account_comm.clone(),
                    rho_randomness,
                    nullifier_gen_counter,
                    nonce,
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    None,
                )
                .unwrap();

                // Verification should fail because pk_enc doesn't match account.sk_enc_inv
                assert!(
                    reg_proof
                        .verify(
                            &mut rng,
                            id,
                            pk_i.0,
                            pk_enc.0,
                            asset_id,
                            &account_comm,
                            nullifier_gen_counter,
                            nonce,
                            account_comm_key.clone(),
                            &account_tree_params.even_parameters.pc_gens(),
                            &account_tree_params.even_parameters.bp_gens(),
                            &poseidon_params,
                            None,
                            None,
                        )
                        .is_err()
                );
            }

            // Encryption secret key used directly (not inverted)

            {
                let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
                let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);

                // Create account with encryption key NOT inverted
                let (account, rho_randomness) = AccountState::new(
                    &mut rng,
                    id,
                    sk_i.0,
                    sk_enc.0.inverse().unwrap(), // Providing inverse so that account state does not inverse
                    asset_id,
                    nullifier_gen_counter,
                    poseidon_params.clone(),
                )
                .unwrap();

                let account_comm = account.commit(account_comm_key.clone()).unwrap();
                let nonce = b"test-nonce-3";

                // Proof creation succeeds with ignore_prover_input_sanitation
                let reg_proof = RegTxnProof::<_, 48, 6>::new(
                    &mut rng,
                    pk_i.0,
                    pk_enc.0,
                    &account,
                    account_comm.clone(),
                    rho_randomness,
                    nullifier_gen_counter,
                    nonce,
                    account_comm_key.clone(),
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                    &poseidon_params,
                    None,
                )
                .unwrap();

                // Verification should fail because account.sk_enc_inv is not the inverse of sk_enc
                assert!(
                    reg_proof
                        .verify(
                            &mut rng,
                            id,
                            pk_i.0,
                            pk_enc.0,
                            asset_id,
                            &account_comm,
                            nullifier_gen_counter,
                            nonce,
                            account_comm_key.clone(),
                            &account_tree_params.even_parameters.pc_gens(),
                            &account_tree_params.even_parameters.bp_gens(),
                            &poseidon_params,
                            None,
                            None,
                        )
                        .is_err()
                );
            }
        }
    }
}
