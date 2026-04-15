use crate::auth_proofs::{AUTH_TXN_LABEL, NULLIFIER_LABEL};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, TXN_CHALLENGE_LABEL,
    add_to_transcript, error::Result,
};
use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::io::Write;
use ark_std::vec::Vec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::Partial2PokPedersenCommitment;

// For new fee account commitment, auth proof will prove
// comm_new_1 = G_{Aff} * sk + G_j * s'
// Host will prove
// comm_new_2 = ... + G_i * rho + G_j * s'', such s = s' + s''
// And verifier will check if comm_new_1 + comm_new_2 == comm_new (the final fee account commitment being inserted into tree)
//
// For old fee account commitment, auth proof will prove
// comm_new_3 = G_{Aff} * sk + B * r'
// Host will prove
// comm_new_4 = ... + G_i * rho + G_j * s + B * r'', such r = r' + r'' where B * r is the blinding used to hide the actual old fee account commitment
// And verifier will check if comm_new_3 + comm_new_4 == comm_old (the re-randomized old fee account commitment whose membership is being proven)

/// For fee account related transactions
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofFeePayment<G: AffineRepr> {
    /// The state (commitment) being invalidated through nullifier
    /// For Pedersen commitment to secret key and part of randomness used to re-randomize the commitment
    pub proof_re_randomized_account_commitment: PokPedersenCommitment<G>,
    /// The new state (commitment) being created
    /// For Pedersen commitment to secret key and part of commitment randomness
    pub proof_updated_account_commitment: Partial2PokPedersenCommitment<G>,
    /// `pk + comm_re_rand_gen * rand_1_old_comm`
    pub partial_re_randomized_account_commitment: G,
    /// `pk + randomness_gen * rand_1_new_comm`
    pub partial_updated_account_commitment: G,
}

impl<G: AffineRepr> AuthProofFeePayment<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        rand_1_old_comm: G::ScalarField, // part of commitment randomness used to re-randomize the old state commitment
        rand_1_new_comm: G::ScalarField, // part of commitment randomness for new state commitment
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        sk_gen: G,
        randomness_gen: G,
        comm_re_rand_gen: G, // generator used to re-randomize the commitment
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

        // For old (re randomized) account commitment `G_aff * sk + B_blinding * rand_1_old_comm` where `rand_1_old_comm` is part of the blinding used in curve tree
        let proto_old = PokPedersenCommitmentProtocol::init(
            sk,
            sk_blinding,
            &sk_gen,
            rand_1_old_comm,
            G::ScalarField::rand(rng),
            &comm_re_rand_gen,
        );

        // For new account commitment `G_aff * sk + G_s * rand_1_new_comm` where `rand_1_new_comm` is part of commitment randomness of new commitment
        let proto_new = PokPedersenCommitmentProtocol::init(
            sk,
            sk_blinding,
            &sk_gen,
            rand_1_new_comm,
            G::ScalarField::rand(rng),
            &randomness_gen,
        );

        let pk = sk_gen * sk;
        let partial_re_randomized_account_commitment =
            (pk + comm_re_rand_gen * rand_1_old_comm).into_affine();
        let partial_updated_account_commitment =
            (pk + randomness_gen * rand_1_new_comm).into_affine();

        proto_old.challenge_contribution(
            &sk_gen,
            &comm_re_rand_gen,
            &partial_re_randomized_account_commitment,
            &mut transcript,
        )?;
        proto_new.challenge_contribution(
            &sk_gen,
            &randomness_gen,
            &partial_updated_account_commitment,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        // old commitment gets the full proof (generates both sk and randomness responses)
        let proof_re_randomized_account_commitment = proto_old.gen_proof(&challenge);
        // new commitment gets the partial proof (sk response is shared from old)
        let proof_updated_account_commitment = proto_new.gen_partial2_proof(&challenge);

        Ok(Self {
            proof_re_randomized_account_commitment,
            proof_updated_account_commitment,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
        })
    }

    pub fn challenge_contribution<W: Write>(
        &self,
        sk_gen: &G,
        current_randomness_gen: &G,
        comm_re_rand_gen: &G,
        mut writer: W,
    ) -> Result<()> {
        self.proof_re_randomized_account_commitment
            .challenge_contribution(
                sk_gen,
                comm_re_rand_gen,
                &self.partial_re_randomized_account_commitment,
                &mut writer,
            )?;

        self.proof_updated_account_commitment
            .challenge_contribution(
                sk_gen,
                current_randomness_gen,
                &self.partial_updated_account_commitment,
                &mut writer,
            )?;
        Ok(())
    }

    pub fn verify_given_challenge(
        &self,
        sk_gen: &G,
        current_randomness_gen: &G,
        comm_re_rand_gen: &G,
        challenge: &G::ScalarField,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        verify_or_rmc_3!(
            rmc,
            self.proof_re_randomized_account_commitment,
            "Failed to verify auth proof for fee payment - old account failed",
            self.partial_re_randomized_account_commitment,
            *sk_gen,
            *comm_re_rand_gen,
            challenge,
        );

        verify_or_rmc_3!(
            rmc,
            self.proof_updated_account_commitment,
            "Failed to verify auth proof for fee payment - new account failed",
            self.partial_updated_account_commitment,
            *sk_gen,
            *current_randomness_gen,
            challenge,
            &self.proof_re_randomized_account_commitment.response1,
        );

        Ok(())
    }

    pub fn verify(
        &self,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &G,
        nullifier: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        sk_gen: G,
        randomness_gen: G,
        comm_re_rand_gen: G, // generator used to re-randomize the commitment
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

        self.challenge_contribution(&sk_gen, &randomness_gen, &comm_re_rand_gen, &mut transcript)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        self.verify_given_challenge(&sk_gen, &randomness_gen, &comm_re_rand_gen, &challenge, rmc)
    }
}
