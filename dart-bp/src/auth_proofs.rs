use crate::account::AccountCommitmentKeyTrait;
use crate::account::state::AccountStateCommitment;
use crate::leg::LegEncryption;
use crate::{
    ACCOUNT_COMMITMENT_LABEL, Error, LEG_ENC_LABEL, NONCE_LABEL, PK_LABEL,
    RE_RANDOMIZED_PATH_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript, error::Result,
};
use ark_ec::{AffineRepr, CurveGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::Partial2PokPedersenCommitment;

// PoC code. Ignoring Poseidon leakage for now. Also assuming device knows encryption key

pub const AUTH_TXN_LABEL: &'static [u8; 8] = b"auth-txn";

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofRegOnlyAffSk<G: AffineRepr> {
    /// For Pedersen commitment to affirmation secret key and part of commitment randomness
    pub proof: PokPedersenCommitment<G>,
    pub partial_account_commitment: G,
}

// Do similar splitting over both old (re-randomized) and updated account commitment
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofAffOnlyAffSk<G: AffineRepr> {
    /// The state (commitment) being invalidated through nullifier
    /// For Pedersen commitment to affirmation secret key and part of randomness used to re-randomize the commitment
    pub proof_re_randomized_account_commitment: Partial2PokPedersenCommitment<G>,
    /// The new state (commitment) being created
    /// For Pedersen commitment to affirmation secret key and part of commitment randomness
    pub proof_updated_account_commitment: PokPedersenCommitment<G>,
    pub partial_re_randomized_account_commitment: G,
    pub partial_updated_account_commitment: G,
}

// Add for mint as well. Also need to support multi-account affirmations as well

impl<G: AffineRepr> AuthProofRegOnlyAffSk<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        rand_1: G::ScalarField, // part of commitment randomness
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

        Self::_prove(
            rng,
            sk_aff,
            rand_1,
            transcript,
            sk_gen,
            current_randomness_gen,
        )
    }

    pub fn verify(
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

        self._verify(transcript, sk_gen, current_randomness_gen)
    }

    fn _prove<R: CryptoRngCore>(
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

    fn _verify(&self, mut transcript: MerlinTranscript, gen_1: G, gen_2: G) -> Result<()> {
        self.proof.challenge_contribution(
            &gen_1,
            &gen_2,
            &self.partial_account_commitment,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        // self.proof.verify(
        //     &self.partial_account_commitment,
        //     &gen_1,
        //     &gen_2,
        //     &challenge,
        // ).ok_or(Error::ProofVerificationError("Failed to verify auth proof".to_string()))
        if !self
            .proof
            .verify(&self.partial_account_commitment, &gen_1, &gen_2, &challenge)
        {
            Err(Error::ProofVerificationError(
                "Failed to verify auth proof".to_string(),
            ))
        } else {
            Ok(())
        }
    }
}

impl<G: AffineRepr> AuthProofAffOnlyAffSk<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        rand_1_old_comm: G::ScalarField, // part of commitment randomness used to re-randomize the old state commitment
        rand_1_new_comm: G::ScalarField, // part of commitment randomness for new state commitment
        leg_enc: &LegEncryption<G>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &AccountStateCommitment<G>,
        nullifier: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        comm_re_rand_gen: G, // generator used to re-randomize the commitment
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            b"nullifier",
            nullifier,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL, // TODO: Choose different label or hash the whole path
            re_randomized_account_commitment,
            ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment,
            LEG_ENC_LABEL,
            leg_enc
        );

        let sk_gen = account_comm_key.sk_gen();
        let current_randomness_gen = account_comm_key.current_randomness_gen();

        let sk_blinding = G::ScalarField::rand(rng);

        // For old (re randomized) account commitment `G_aff * sk + B_blinding * rand_1_old_comm` where `rand_1_old_comm` is part of the blinding used in curve tree
        let proto1 = PokPedersenCommitmentProtocol::init(
            sk_aff,
            sk_blinding,
            &sk_gen,
            rand_1_old_comm,
            G::ScalarField::rand(rng),
            &comm_re_rand_gen,
        );

        // For new account commitment `G_aff * sk + G_s * rand_1_new_comm` where `rand_1_new_comm` is part of commitment randomness of new commiment
        let proto2 = PokPedersenCommitmentProtocol::init(
            sk_aff,
            sk_blinding,
            &sk_gen,
            rand_1_new_comm,
            G::ScalarField::rand(rng),
            &current_randomness_gen,
        );

        let partial_re_randomized_account_commitment =
            (sk_gen * sk_aff + comm_re_rand_gen * rand_1_old_comm).into_affine();
        let partial_updated_account_commitment =
            (sk_gen * sk_aff + current_randomness_gen * rand_1_new_comm).into_affine();

        proto1.challenge_contribution(
            &sk_gen,
            &comm_re_rand_gen,
            &partial_re_randomized_account_commitment,
            &mut transcript,
        )?;

        proto2.challenge_contribution(
            &sk_gen,
            &current_randomness_gen,
            &partial_updated_account_commitment,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let proof_updated_account_commitment = proto2.gen_proof(&challenge);
        let proof_re_randomized_account_commitment = proto1.gen_partial2_proof(&challenge);

        Ok(Self {
            proof_re_randomized_account_commitment,
            proof_updated_account_commitment,
            partial_re_randomized_account_commitment,
            partial_updated_account_commitment,
        })
    }

    pub fn verify(
        &self,
        leg_enc: &LegEncryption<G>,
        re_randomized_account_commitment: &G,
        updated_account_commitment: &AccountStateCommitment<G>,
        nullifier: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        comm_re_rand_gen: G, // generator used to re-randomize the commitment
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            b"nullifier",
            nullifier,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_account_commitment,
            ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment,
            LEG_ENC_LABEL,
            leg_enc
        );

        let sk_gen = account_comm_key.sk_gen();
        let current_randomness_gen = account_comm_key.current_randomness_gen();

        self.proof_re_randomized_account_commitment
            .challenge_contribution(
                &sk_gen,
                &comm_re_rand_gen,
                &self.partial_re_randomized_account_commitment,
                &mut transcript,
            )?;

        self.proof_updated_account_commitment
            .challenge_contribution(
                &sk_gen,
                &current_randomness_gen,
                &self.partial_updated_account_commitment,
                &mut transcript,
            )?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        if !self.proof_updated_account_commitment.verify(
            &self.partial_updated_account_commitment,
            &sk_gen,
            &current_randomness_gen,
            &challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Failed to verify auth proof for affirmation - new account failed".to_string(),
            ));
        }

        if !self.proof_re_randomized_account_commitment.verify(
            &self.partial_re_randomized_account_commitment,
            &sk_gen,
            &comm_re_rand_gen,
            &challenge,
            &self.proof_updated_account_commitment.response1,
        ) {
            return Err(Error::ProofVerificationError(
                "Failed to verify auth proof for affirmation - old account failed".to_string(),
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    // use ark_pallas::PallasConfig;
    // use ark_vesta::VestaConfig;
    // use curve_tree_relations::curve_tree::CurveTree;
    use super::*;
    use crate::account::tests::{setup_gens_new, setup_leg_with_conf};
    use crate::account_registration::tests::{new_account, setup_comm_key};
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::leg::LegEncConfig;
    use crate::leg::tests::setup_keys;

    type Fr = ark_pallas::Fr;
    type PallasA = ark_pallas::Affine;

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

        let (account, _, _, _) = new_account(&mut rng, asset_id, sk_i.clone(), sk_enc, id);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // Only hardware (Ledger) knows these 2
        let rand_1 = Fr::rand(&mut rng);
        // let rand_2 = account.randomness - rand_1;

        // Host creates its proof over this commitment. Chain will get this as public input
        let host_commitment = (account_comm.0
            - (account_comm_key.sk_gen() * sk_i.0)
            - (account_comm_key.current_randomness_gen() * rand_1))
            .into_affine();

        // Proof done by device
        let nonce = b"test-nonce";

        let proof = AuthProofRegOnlyAffSk::new(
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
            .verify(pk_i.0, &account_comm, nonce, account_comm_key)
            .unwrap();

        assert_eq!(
            host_commitment + proof.partial_account_commitment,
            account_comm.0
        );
    }

    #[test]
    fn affirmation() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2
        // const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;

        // All parties generate their keys
        let (((sk_s, _), (sk_s_e, pk_s_e)), (_, (_, pk_r_e)), ((_, _), (_, pk_a_e))) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let id = Fr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, sk_s.clone(), sk_s_e, id);
        // account is not new and doing some state transition
        account.balance += 100;
        account.counter += 1;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // let set = vec![account_comm.0];
        // let account_tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
        //     &set,
        //     &account_tree_params,
        //     Some(5),
        // );

        let leaf_blinding = Fr::rand(&mut rng);
        // Curve tree proof will also randomize it this way
        let re_randomized_account_commitment = (account_comm.0
            + (account_tree_params.even_parameters.pc_gens().B_blinding * leaf_blinding))
            .into_affine();

        let updated_account = account.get_state_for_send(10).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        // let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: false,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_a_e.0,
            None,
            10,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            account_comm_key.sk_enc_gen(),
            enc_gen,
        );

        // Only hardware (Ledger) knows these
        let rand_1_old = Fr::rand(&mut rng);
        // let rand_1_new = leaf_blinding - rand_1_old;
        let rand_1_new = Fr::rand(&mut rng);
        // let rand_2_new = updated_account.randomness - rand_1_new;

        // Host creates its proof over these commitments. Chain will get these as public input
        let host_commitment_old = (re_randomized_account_commitment
            - (account_comm_key.sk_gen() * sk_s.0)
            - (account_tree_params.even_parameters.pc_gens().B_blinding * rand_1_old))
            .into_affine();

        let host_commitment_new = (updated_account_comm.0
            - (account_comm_key.sk_gen() * sk_s.0)
            - (account_comm_key.current_randomness_gen() * rand_1_new))
            .into_affine();

        // Creating random nullifier for testing, in practice this should come from host
        let nullifier = PallasA::rand(&mut rng);

        // Proof done by device

        let nonce = b"test-nonce";

        let proof = AuthProofAffOnlyAffSk::new(
            &mut rng,
            sk_s.0,
            rand_1_old,
            rand_1_new,
            &leg_enc,
            &re_randomized_account_commitment,
            &updated_account_comm,
            nullifier,
            nonce,
            account_comm_key.clone(),
            account_tree_params.even_parameters.pc_gens().B_blinding,
        )
        .unwrap();

        proof
            .verify(
                &leg_enc,
                &re_randomized_account_commitment,
                &updated_account_comm,
                nullifier,
                nonce,
                account_comm_key.clone(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
            )
            .unwrap();

        assert_eq!(
            host_commitment_old + proof.partial_re_randomized_account_commitment,
            re_randomized_account_commitment
        );

        assert_eq!(
            host_commitment_new + proof.partial_updated_account_commitment,
            updated_account_comm.0
        );
    }
}
