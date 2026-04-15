pub mod account;
pub mod fee_account;
pub mod helpers;
pub mod transparent;

use crate::{
    NONCE_LABEL, PK_ENC_LABEL, PK_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript, error::Result,
};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::io::Write;
use ark_std::vec::Vec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol};
use schnorr_pok::partial::{Partial2PokPedersenCommitment, PartialPokDiscreteLog};

pub const AUTH_TXN_LABEL: &'static [u8; 8] = b"auth-txn";
pub const NULLIFIER_LABEL: &[u8; 9] = b"nullifier";

#[derive(Clone, Debug)]
pub struct AuthProofOnlySksProtocol<G: AffineRepr> {
    pub proto_aff: PokDiscreteLogProtocol<G>,
    pub proto_enc: PokDiscreteLogProtocol<G>,
}

/// Authorization proof proving knowledge of both secret keys and assumes the public keys are revealed. This applies during registration and miniting.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofOnlySks<G: AffineRepr> {
    /// Proving knowledge of affirmation secret key
    pub proof_afk: PokDiscreteLog<G>,
    /// Proving knowledge of encryption secret key
    pub proof_enc: PokDiscreteLog<G>,
}

#[derive(Clone, Debug)]
pub struct AuthProofOnlySkProtocol<G: AffineRepr>(pub PokDiscreteLogProtocol<G>);

/// Authorization proof proving knowledge of single secret key and assumes the public key is revealed. This applies during fee registration and fee topup.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuthProofOnlySk<G: AffineRepr>(pub PokDiscreteLog<G>);

impl<G: AffineRepr> AuthProofOnlySksProtocol<G> {
    pub fn init<R: CryptoRngCore, W: Write>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        sk_enc: G::ScalarField,
        pk_aff: &G,
        pk_enc: &G,
        sk_aff_gen: &G,
        sk_enc_gen: &G,
        mut writer: W,
    ) -> Result<Self> {
        let proto_aff = PokDiscreteLogProtocol::init(sk_aff, G::ScalarField::rand(rng), sk_aff_gen);
        let proto_enc = PokDiscreteLogProtocol::init(sk_enc, G::ScalarField::rand(rng), sk_enc_gen);
        proto_aff.challenge_contribution(sk_aff_gen, pk_aff, &mut writer)?;
        proto_enc.challenge_contribution(sk_enc_gen, pk_enc, &mut writer)?;
        Ok(Self {
            proto_aff,
            proto_enc,
        })
    }

    pub fn gen_proof(self, challenge: &G::ScalarField) -> AuthProofOnlySks<G> {
        let proof_afk = self.proto_aff.gen_proof(challenge);
        let proof_enc = self.proto_enc.gen_proof(challenge);
        AuthProofOnlySks {
            proof_afk,
            proof_enc,
        }
    }
}

impl<G: AffineRepr> AuthProofOnlySks<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        sk_enc: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        sk_aff_gen: &G,
        sk_enc_gen: &G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            PK_LABEL,
            pk_aff,
            PK_ENC_LABEL,
            pk_enc,
        );

        let proto = AuthProofOnlySksProtocol::init(
            rng,
            sk_aff,
            sk_enc,
            &pk_aff,
            &pk_enc,
            sk_aff_gen,
            sk_enc_gen,
            &mut transcript,
        )?;
        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        let proof = proto.gen_proof(&challenge);
        Ok(proof)
    }

    pub fn verify(
        &self,
        pk_aff: G,
        pk_enc: G,
        nonce: &[u8], // This could be the same nonce used by host device or a concatenation of host's nonce and other data like its challenge (if doing sequential)
        sk_aff_gen: &G,
        sk_enc_gen: &G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            PK_LABEL,
            pk_aff,
            PK_ENC_LABEL,
            pk_enc,
        );

        self.challenge_contribution(&pk_aff, &pk_enc, sk_aff_gen, sk_enc_gen, &mut transcript)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        self.verify_given_challenge(&pk_aff, &pk_enc, sk_aff_gen, sk_enc_gen, &challenge, rmc)
    }

    pub fn challenge_contribution<W: Write>(
        &self,
        pk_aff: &G,
        pk_enc: &G,
        sk_aff_gen: &G,
        sk_enc_gen: &G,
        mut writer: W,
    ) -> Result<()> {
        self.proof_afk
            .challenge_contribution(sk_aff_gen, pk_aff, &mut writer)?;

        self.proof_enc
            .challenge_contribution(sk_enc_gen, pk_enc, &mut writer)?;
        Ok(())
    }

    pub fn verify_given_challenge(
        &self,
        pk_aff: &G,
        pk_enc: &G,
        sk_aff_gen: &G,
        sk_enc_gen: &G,
        challenge: &G::ScalarField,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        verify_or_rmc_2!(
            rmc,
            self.proof_afk,
            "Failed to verify auth proof with affirmation key",
            *pk_aff,
            *sk_aff_gen,
            &challenge,
        );

        verify_or_rmc_2!(
            rmc,
            self.proof_enc,
            "Failed to verify auth proof with encryption key",
            *pk_enc,
            *sk_enc_gen,
            &challenge,
        );

        Ok(())
    }
}

impl<G: AffineRepr> AuthProofOnlySkProtocol<G> {
    pub fn init<R: CryptoRngCore, W: Write>(
        rng: &mut R,
        sk: G::ScalarField,
        pk: &G,
        sk_gen: &G,
        mut writer: W,
    ) -> Result<Self> {
        let proto = PokDiscreteLogProtocol::init(sk, G::ScalarField::rand(rng), sk_gen);
        proto.challenge_contribution(sk_gen, pk, &mut writer)?;
        Ok(AuthProofOnlySkProtocol(proto))
    }

    pub fn gen_proof(self, challenge: &G::ScalarField) -> AuthProofOnlySk<G> {
        AuthProofOnlySk(self.0.gen_proof(challenge))
    }
}

impl<G: AffineRepr> AuthProofOnlySk<G> {
    /// Create a standalone auth proof with its own `AUTH_TXN_LABEL` transcript.
    /// `nonce` binds this proof to a context (e.g. the host's partial challenge bytes).
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        pk: G,
        nonce: &[u8],
        sk_gen: &G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
        add_to_transcript!(transcript, NONCE_LABEL, nonce);
        let proto = AuthProofOnlySkProtocol::init(rng, sk, &pk, sk_gen, &mut transcript)?;
        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        Ok(proto.gen_proof(&challenge))
    }

    pub fn verify(
        &self,
        pk: G,
        nonce: &[u8],
        sk_gen: &G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
        add_to_transcript!(transcript, NONCE_LABEL, nonce);
        self.challenge_contribution(&pk, sk_gen, &mut transcript)?;
        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        self.verify_given_challenge(&pk, sk_gen, &challenge, rmc)
    }

    pub fn challenge_contribution<W: Write>(
        &self,
        pk: &G,
        sk_gen: &G,
        mut writer: W,
    ) -> Result<()> {
        self.0.challenge_contribution(sk_gen, pk, &mut writer)?;
        Ok(())
    }

    pub fn verify_given_challenge(
        &self,
        pk: &G,
        sk_gen: &G,
        challenge: &G::ScalarField,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        verify_or_rmc_2!(
            rmc,
            self.0,
            "Failed to verify auth proof with secret key",
            *pk,
            *sk_gen,
            challenge,
        );
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account::tests::{setup_gens_new, setup_leg_with_conf};
    use crate::account::{AccountCommitmentKeyTrait, LegProverConfig, LegVerifierConfig};
    use crate::account_registration::tests::{new_account, setup_comm_key};
    use crate::auth_proofs::account::AuthProofAffirmation;
    use crate::auth_proofs::fee_account::AuthProofFeePayment;
    use crate::auth_proofs::transparent::AuthProofTransparent;
    use crate::fee_account::tests::new_fee_account;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::leg::tests::setup_keys;
    use crate::leg::{LegEncConfig, PartyEphemeralPublicKey};
    use ark_ec::CurveGroup;

    type Fr = ark_pallas::Fr;
    type PallasA = ark_pallas::Affine;

    #[test]
    fn registration() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        // Investor creates keys
        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);

        // Proof done by device
        let nonce = b"test-nonce";

        let proof = AuthProofOnlySks::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            pk_aff.0,
            pk_enc.0,
            nonce,
            &account_comm_key.sk_gen(),
            &account_comm_key.sk_enc_gen(),
        )
        .unwrap();

        proof
            .verify(
                pk_aff.0,
                pk_enc.0,
                nonce,
                &account_comm_key.sk_gen(),
                &account_comm_key.sk_enc_gen(),
                None,
            )
            .unwrap();
    }

    #[test]
    fn fee_payment_auth() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2
        // const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;

        // All parties generate their keys
        let (((sk_s, pk_s), _), (_, _), _) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let account = new_fee_account(&mut rng, asset_id, sk_s.clone(), 100);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let leaf_blinding = Fr::rand(&mut rng);
        // Curve tree proof will also randomize it this way
        let re_randomized_account_commitment = (account_comm.0
            + (account_tree_params.even_parameters.pc_gens().B_blinding * leaf_blinding))
            .into_affine();

        let updated_account = account.get_state_for_payment(10).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        // Only hardware (Ledger) knows these
        let rand_1_old = Fr::rand(&mut rng);
        // let rand_1_new = leaf_blinding - rand_1_old;
        let rand_1_new = Fr::rand(&mut rng);
        // let rand_2_new = updated_account.randomness - rand_1_new;

        // Host creates its proof over these commitments. Chain will get these as public input
        let host_commitment_old = (re_randomized_account_commitment
            - pk_s.0
            - (account_tree_params.even_parameters.pc_gens().B_blinding * rand_1_old))
            .into_affine();

        let host_commitment_new = (updated_account_comm.0
            - pk_s.0
            - (account_comm_key.current_randomness_gen() * rand_1_new))
            .into_affine();

        // Creating random nullifier for testing, in practice this should come from host
        let nullifier = PallasA::rand(&mut rng);

        // Proof done by device

        let nonce = b"test-nonce";

        let proof = AuthProofFeePayment::new(
            &mut rng,
            sk_s.0,
            rand_1_old,
            rand_1_new,
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            account_comm_key.current_randomness_gen(),
            account_tree_params.even_parameters.pc_gens().B_blinding,
        )
        .unwrap();

        proof
            .verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                account_comm_key.sk_gen(),
                account_comm_key.current_randomness_gen(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
                None,
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

    #[test]
    fn transparent_auth() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let enc_key_gen = account_comm_key.sk_enc_gen();

        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let id = Fr::rand(&mut rng);

        let (mut account, _, _, _) =
            new_account(&mut rng, asset_id, sk_aff.clone(), sk_enc.clone(), id);
        account.without_sk.balance = 100;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let updated_account = account.get_state_for_withdraw(30).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let leaf_blinding = Fr::rand(&mut rng);
        let pc_gens = account_tree_params.even_parameters.pc_gens();
        let b_blinding = pc_gens.B_blinding;
        let re_randomized_account_commitment =
            (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();

        // Only hardware (Ledger) knows these
        let rand_part_old_comm = Fr::rand(&mut rng);
        let rand_new_comm = Fr::rand(&mut rng);

        let nullifier = PallasA::rand(&mut rng);
        let nonce = b"test-nonce";

        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let proof = AuthProofTransparent::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            rand_part_old_comm,
            rand_new_comm,
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            auditor_pubkeys.clone(),
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
        )
        .unwrap();

        proof
            .verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                nonce,
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                None,
            )
            .unwrap();

        // Verify partial commitments sum correctly
        let pk = pk_aff.0 + pk_enc.0;
        let host_commitment_old =
            (re_randomized_account_commitment - pk - (b_blinding * rand_part_old_comm))
                .into_affine();
        let host_commitment_new =
            (updated_account_comm.0 - pk - (b_blinding * rand_new_comm)).into_affine();

        assert_eq!(
            host_commitment_old + proof.partial_re_randomized_account_commitment,
            re_randomized_account_commitment
        );
        assert_eq!(
            host_commitment_new + proof.partial_updated_account_commitment,
            updated_account_comm.0
        );

        // Verify decryption works
        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(proof.encrypted_pubkeys.decrypt(i, sk.0), pk_aff.0);
        }
    }

    #[test]
    fn affirmation_auth() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        let (account_tree_params, account_comm_key, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let amount = 100;
        let enc_key_gen = account_comm_key.sk_enc_gen();

        let (((sk_aff, pk_aff), (sk_enc, pk_enc)), (_, (_, pk_r_e)), _) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let id = Fr::rand(&mut rng);

        let (mut account, _, _, _) =
            new_account(&mut rng, asset_id, sk_aff.clone(), sk_enc.clone(), id);
        account.without_sk.balance = 200;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let updated_account = account.get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

        let leaf_blinding = Fr::rand(&mut rng);
        let re_randomized_account_commitment =
            (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();

        // Auth's shares of the rerandomization
        let rand_part_old_comm = Fr::rand(&mut rng);
        let rand_new_comm = Fr::rand(&mut rng);

        let nullifier = PallasA::rand(&mut rng);
        let nonce = b"test-nonce";

        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: false,
        };

        let (_, leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            conf,
            pk_enc.0,
            None,
            amount,
            asset_id,
            pk_enc.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (leg_enc_core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();

        let k_1 = Fr::rand(&mut rng);
        let k_2 = Fr::rand(&mut rng);

        let legs_prover = vec![LegProverConfig {
            encryption: leg_enc_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
            has_balance_changed: true,
        }];

        let proof = AuthProofAffirmation::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            rand_part_old_comm,
            rand_new_comm,
            vec![k_1],
            vec![k_2],
            legs_prover,
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
        )
        .unwrap();

        let legs_verifier = vec![LegVerifierConfig {
            encryption: leg_enc_core,
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
            has_balance_decreased: Some(true),
            has_counter_decreased: None,
        }];

        proof
            .verify(
                legs_verifier,
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            )
            .unwrap();

        // Verify partial commitments sum correctly
        let pk = pk_aff.0 + pk_enc.0;
        let host_commitment_old =
            (re_randomized_account_commitment - pk - (b_blinding * rand_part_old_comm))
                .into_affine();
        let host_commitment_new =
            (updated_account_comm.0 - pk - (b_blinding * rand_new_comm)).into_affine();

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
