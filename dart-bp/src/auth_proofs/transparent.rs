use crate::account::transparent::{
    EncryptedPublicKey, chal_contrib_pk_enc, init_pk_enc_protocol, reps_pk_enc, verify_pk_enc,
};
use crate::auth_proofs::helpers::{init_acc_comm_protocol, verify_acc_comm};
use crate::auth_proofs::{AUTH_TXN_LABEL, NULLIFIER_LABEL, helpers};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, TXN_CHALLENGE_LABEL,
    add_to_transcript, error::Result,
};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::io::Write;
use ark_std::{UniformRand, vec::Vec};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::SchnorrResponse;
use schnorr_pok::partial::{
    Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
};

// For new account commitment, auth proof will prove
// comm_new_1 = G_{Aff} * sk + G_{Enc} * sk_enc + B * r
// Host will prove
// comm_new_2 = ... + G_j * rho + G_k * rho^i + G_l * s + G_m * s^i + B * -r
// And verifier will check if comm_new_1 + comm_new_2 == comm_new (the final account commitment being inserted into tree)
// This is done as relations involving rho, rho^i, s, s_i need to be proven in BP

/// For non-fee account related transparent transactions, like deposit and withdraw
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofTransparent<G: AffineRepr> {
    /// The state (commitment) being invalidated through nullifier
    /// For Pedersen commitment to affirmation secret key, encryption secret key and part of randomness used to re-randomize the commitment
    pub t_re_randomized_account_commitment: G,
    pub resp_re_randomized_account_commitment: SchnorrResponse<G>,
    /// The new state (commitment) being created
    /// For Pedersen commitment to affirmation secret key, encryption secret key and part of commitment randomness
    pub t_updated_account_commitment: G,
    pub resp_updated_account_commitment: PartialSchnorrResponse<G>,
    /// `sk_gen * sk + enc_key_gen * sk_enc + comm_re_rand_gen * rand_part_old_comm`
    pub partial_re_randomized_account_commitment: G,
    /// `sk_gen * sk + enc_key_gen * sk_enc + comm_re_rand_gen * rand_new_comm`
    pub partial_updated_account_commitment: G,
    resp_eph_pk: Vec<PartialPokDiscreteLog<G>>,
    resp_enc: Partial1PokPedersenCommitment<G>,
    pub encrypted_pubkeys: EncryptedPublicKey<G>,
}

impl<G: AffineRepr> AuthProofTransparent<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        sk_enc: G::ScalarField,
        rand_part_old_comm: G::ScalarField, // part of commitment randomness used to re-randomize the old state commitment
        rand_new_comm: G::ScalarField, // new randomness used to blind this part of new account commitment
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        auditor_keys: Vec<G>,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NULLIFIER_LABEL,
            nullifier,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL, // TODO: Choose different label or hash the whole path
            re_randomized_account_commitment,
            ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let sk_blinding = G::ScalarField::rand(rng);
        let sk_enc_blinding = G::ScalarField::rand(rng);

        let (
            proto_old,
            proto_new,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
        ) = init_acc_comm_protocol(
            rng,
            sk,
            sk_enc,
            rand_part_old_comm,
            rand_new_comm,
            sk_blinding,
            sk_enc_blinding,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            &mut transcript,
        )?;

        let (t_eph_pk, t_enc, encrypted_pubkey) = init_pk_enc_protocol(
            rng,
            sk,
            sk_blinding,
            auditor_keys,
            sk_gen,
            enc_key_gen,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let (resp_eph_pk, reps_enc) = reps_pk_enc(t_eph_pk, t_enc, &challenge);
        let (resp_re_randomized_account_commitment, resp_updated_account_commitment) =
            helpers::resp_acc_comm(
                sk,
                sk_enc,
                rand_part_old_comm,
                rand_new_comm,
                &proto_old,
                &proto_new,
                &challenge,
            )?;

        Ok(Self {
            t_re_randomized_account_commitment: proto_old.t,
            resp_re_randomized_account_commitment,
            t_updated_account_commitment: proto_new.t,
            resp_updated_account_commitment,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
            resp_eph_pk,
            resp_enc: reps_enc,
            encrypted_pubkeys: encrypted_pubkey,
        })
    }

    pub fn verify(
        &self,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        auditor_keys: &[G],
        nonce: &[u8],
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G, // generator used blind the old and new commitment parts
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NULLIFIER_LABEL,
            nullifier,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_account_commitment,
            ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        self.challenge_contribution(&auditor_keys, sk_gen, enc_key_gen, &mut transcript)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        self.verify_given_challenge(
            auditor_keys,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            &challenge,
            rmc,
        )
    }

    pub fn challenge_contribution<W: Write>(
        &self,
        auditor_keys: &[G],
        sk_gen: G,
        enc_key_gen: G,
        mut writer: W,
    ) -> Result<()> {
        self.t_re_randomized_account_commitment
            .serialize_compressed(&mut writer)?;
        self.partial_re_randomized_account_commitment
            .serialize_compressed(&mut writer)?;
        self.t_updated_account_commitment
            .serialize_compressed(&mut writer)?;
        self.partial_updated_account_commitment
            .serialize_compressed(&mut writer)?;

        chal_contrib_pk_enc(
            &self.resp_eph_pk,
            &self.resp_enc,
            &self.encrypted_pubkeys,
            auditor_keys,
            sk_gen,
            enc_key_gen,
            &mut writer,
        )?;

        Ok(())
    }

    pub fn verify_given_challenge(
        &self,
        auditor_keys: &[G],
        sk_gen: G,
        enc_key_gen: G,
        comm_re_rand_gen: G,
        challenge: &G::ScalarField,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        verify_acc_comm(
            &self.partial_re_randomized_account_commitment,
            &self.t_re_randomized_account_commitment,
            &self.resp_re_randomized_account_commitment,
            &self.partial_updated_account_commitment,
            &self.t_updated_account_commitment,
            &self.resp_updated_account_commitment,
            &challenge,
            sk_gen,
            enc_key_gen,
            comm_re_rand_gen,
            rmc.as_deref_mut(),
        )?;

        // Verify pk encryption proofs (sk_response is index 0 from old commitment's full response)
        verify_pk_enc(
            &self.resp_eph_pk,
            &self.resp_enc,
            &self.encrypted_pubkeys,
            auditor_keys,
            challenge,
            &self.resp_re_randomized_account_commitment.0[0],
            sk_gen,
            enc_key_gen,
            rmc,
        )?;

        Ok(())
    }
}
