use crate::account::AccountCommitmentKeyTrait;
use crate::account::state::AccountStateCommitment;
use crate::leg::LegEncryption;
use crate::{
    ACCOUNT_COMMITMENT_LABEL, Error, LEG_ENC_LABEL, NONCE_LABEL, PK_LABEL, TXN_CHALLENGE_LABEL,
    add_to_transcript, error::Result,
};
use ark_ec::{AffineRepr, CurveGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokPedersenCommitment, PokPedersenCommitmentProtocol};

// PoC code. Ignoring Poseidon leakage for now

pub const AUTH_TXN_LABEL: &'static [u8; 8] = b"auth-txn";

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofOnlyAffSk<G: AffineRepr> {
    pub proof: PokPedersenCommitment<G>,
    pub partial_account_commitment: G,
}

impl<G: AffineRepr> AuthProofOnlyAffSk<G> {
    pub fn new_for_reg<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        rand_1: G::ScalarField,
        pk_aff: G,
        account_commitment: &AccountStateCommitment<G>,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk_aff,
        );

        let sk_gen = account_comm_key.sk_gen();
        let current_randomness_gen = account_comm_key.current_randomness_gen();

        let proto = PokPedersenCommitmentProtocol::init(
            sk_aff,
            G::ScalarField::rand(rng),
            &sk_gen,
            rand_1,
            G::ScalarField::rand(rng),
            &current_randomness_gen,
        );

        let partial_account_commitment =
            (sk_gen * sk_aff + current_randomness_gen * rand_1).into_affine();
        proto.challenge_contribution(
            &sk_gen,
            &current_randomness_gen,
            &partial_account_commitment,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let proof = proto.gen_proof(&challenge);

        Ok(Self {
            proof,
            partial_account_commitment,
        })
    }

    pub fn new_for_aff<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        rand_1: G::ScalarField,
        leg_enc: LegEncryption<G>,
        updated_account_commitment: &AccountStateCommitment<G>,
        nullifier: G,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        comm_re_rand_gen: &G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment,
            LEG_ENC_LABEL,
            leg_enc
        );

        todo!()
    }

    // Add for mint as well. Also need to support multi-account affirmations as well

    pub fn verify_for_reg(
        &self,
        pk_aff: G,
        account_commitment: &AccountStateCommitment<G>,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk_aff,
        );

        let sk_gen = account_comm_key.sk_gen();
        let current_randomness_gen = account_comm_key.current_randomness_gen();

        self.proof.challenge_contribution(
            &sk_gen,
            &current_randomness_gen,
            &self.partial_account_commitment,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        // self.proof.verify(
        //     &self.partial_account_commitment,
        //     &sk_gen,
        //     &current_randomness_gen,
        //     &challenge,
        // ).ok_or(Error::ProofVerificationError("Failed to verify auth proof".to_string()))
        if !self.proof.verify(
            &self.partial_account_commitment,
            &sk_gen,
            &current_randomness_gen,
            &challenge,
        ) {
            Err(Error::ProofVerificationError(
                "Failed to verify auth proof".to_string(),
            ))
        } else {
            Ok(())
        }
    }

    fn prove<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        rand_1: G::ScalarField,
        mut transcript: MerlinTranscript,
        gen_1: G,
        gen_2: G,
    ) -> Result<Self> {
        let proto = PokPedersenCommitmentProtocol::init(
            sk_aff,
            G::ScalarField::rand(rng),
            &gen_1,
            rand_1,
            G::ScalarField::rand(rng),
            &gen_2,
        );

        let partial_account_commitment = (gen_1 * sk_aff + gen_2 * rand_1).into_affine();
        proto.challenge_contribution(
            &gen_1,
            &gen_2,
            &partial_account_commitment,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let proof = proto.gen_proof(&challenge);

        Ok(Self {
            proof,
            partial_account_commitment,
        })
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account_registration::tests::{new_account, setup_comm_key};
    use crate::keys::{keygen_enc, keygen_sig};

    type Fr = ark_pallas::Fr;

    #[test]
    fn registration() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;

        // Investor creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let id = Fr::rand(&mut rng);

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);

        let (account, _, _) = new_account(&mut rng, asset_id, sk_i.clone(), sk_enc, id);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // Only hardware (Ledger) knows these 2
        let rand_1 = Fr::rand(&mut rng);
        let rand_2 = account.randomness - rand_1;

        let host_commitment = (account_comm.0
            - (account_comm_key.sk_gen() * sk_i.0)
            - (account_comm_key.current_randomness_gen() * rand_1))
            .into_affine();

        let nonce = b"test-nonce";

        let proof = AuthProofOnlyAffSk::new_for_reg(
            &mut rng,
            sk_i.0,
            rand_1,
            pk_i.0,
            &account_comm,
            nonce,
            account_comm_key.clone(),
        )
        .unwrap();

        proof
            .verify_for_reg(pk_i.0, &account_comm, nonce, account_comm_key)
            .unwrap();

        assert_eq!(
            host_commitment + proof.partial_account_commitment,
            account_comm.0
        );
    }
}
