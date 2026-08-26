pub mod account;
pub mod fee_account;
pub mod helpers;
pub mod transparent;

use crate::{
    NONCE_LABEL, PK_ENC_LABEL, PK_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript, dst, error::Result,
};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::io::Write;
use ark_std::vec::Vec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol};
use schnorr_pok::partial::{Partial2PokPedersenCommitment, PartialPokDiscreteLog};

pub const AUTH_TXN_LABEL: &'static [u8; 8] = b"auth-txn";
pub const NULLIFIER_LABEL: &[u8; 9] = b"nullifier";

pub const DEVICE_TXN_TYPE_LABEL: &[u8] = b"device-txn-type";
pub const DEVICE_ASSET_ID_LABEL: &[u8] = b"device-asset-id";
pub const DEVICE_AMOUNT_LABEL: &[u8] = b"device-amount";
pub const DEVICE_AFFIRM_TYPE_LABEL: &[u8] = b"device-affirm-type";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeviceAffirmationType {
    SenderAffirmation,
    ReceiverAffirmation,
    ReceiverClaim,
    SenderReversal,
    ReceiverReversal,
    SenderCounterUpdate,
    ReceiverCounterUpdate,
    InstantSenderAffirmation,
    InstantReceiverAffirmation,
}

impl DeviceAffirmationType {
    pub fn typ(&self) -> u8 {
        match self {
            DeviceAffirmationType::SenderAffirmation => 0,
            DeviceAffirmationType::ReceiverAffirmation => 1,
            DeviceAffirmationType::ReceiverClaim => 2,
            DeviceAffirmationType::SenderReversal => 3,
            DeviceAffirmationType::ReceiverReversal => 4,
            DeviceAffirmationType::SenderCounterUpdate => 5,
            DeviceAffirmationType::ReceiverCounterUpdate => 6,
            DeviceAffirmationType::InstantSenderAffirmation => 7,
            DeviceAffirmationType::InstantReceiverAffirmation => 8,
        }
    }
}

/// The txn type a device is authorizing in a split proof. Added to the device transcript binding
/// the txn shown to the device to the proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeviceTxnType {
    AccountRegistration { asset_id: AssetId },
    Mint { asset_id: AssetId, amount: Balance },
    FeeAccountRegistration { asset_id: AssetId },
    FeeAccountTopup { asset_id: AssetId, amount: Balance },
    FeePayment { asset_id: AssetId, amount: Balance },
    DeviceAffirmation { typ: DeviceAffirmationType },
    Deposit { asset_id: AssetId, amount: Balance },
    Withdraw { asset_id: AssetId, amount: Balance },
}

impl DeviceTxnType {
    pub fn txn_type(&self) -> u8 {
        match self {
            DeviceTxnType::AccountRegistration { .. } => 0,
            DeviceTxnType::Mint { .. } => 1,
            DeviceTxnType::FeeAccountRegistration { .. } => 2,
            DeviceTxnType::FeeAccountTopup { .. } => 3,
            DeviceTxnType::FeePayment { .. } => 4,
            DeviceTxnType::DeviceAffirmation { .. } => 5,
            DeviceTxnType::Deposit { .. } => 6,
            DeviceTxnType::Withdraw { .. } => 7,
        }
    }

    /// Absorb the transaction type and its consent-relevant parameters into `transcript`.
    pub fn add_to_transcript(&self, transcript: &mut MerlinTranscript) -> Result<()> {
        let txn_type = self.txn_type();
        match self {
            DeviceTxnType::AccountRegistration { asset_id }
            | DeviceTxnType::FeeAccountRegistration { asset_id } => {
                add_to_transcript!(
                    transcript,
                    DEVICE_TXN_TYPE_LABEL,
                    txn_type,
                    DEVICE_ASSET_ID_LABEL,
                    *asset_id
                );
            }
            DeviceTxnType::Mint { asset_id, amount }
            | DeviceTxnType::FeeAccountTopup { asset_id, amount }
            | DeviceTxnType::FeePayment { asset_id, amount }
            | DeviceTxnType::Deposit { asset_id, amount }
            | DeviceTxnType::Withdraw { asset_id, amount } => {
                add_to_transcript!(
                    transcript,
                    DEVICE_TXN_TYPE_LABEL,
                    txn_type,
                    DEVICE_ASSET_ID_LABEL,
                    *asset_id,
                    DEVICE_AMOUNT_LABEL,
                    *amount
                );
            }
            DeviceTxnType::DeviceAffirmation { typ } => {
                add_to_transcript!(
                    transcript,
                    DEVICE_TXN_TYPE_LABEL,
                    txn_type,
                    DEVICE_AFFIRM_TYPE_LABEL,
                    typ.typ()
                );
            }
        }
        Ok(())
    }
}

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
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        sk_aff: G::ScalarField,
        sk_enc: G::ScalarField,
        pk_aff: &G,
        pk_enc: &G,
        sk_aff_gen: &G,
        sk_enc_gen: &G,
        transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        let proto_aff = PokDiscreteLogProtocol::init(sk_aff, G::ScalarField::rand(rng), sk_aff_gen);
        let proto_enc = PokDiscreteLogProtocol::init(sk_enc, G::ScalarField::rand(rng), sk_enc_gen);
        proto_aff.challenge_contribution(sk_aff_gen, pk_aff, dst::AUTH_SK_AFF, transcript)?;
        proto_enc.challenge_contribution(sk_enc_gen, pk_enc, dst::AUTH_SK_ENC, transcript)?;
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
        txn_type: &DeviceTxnType,
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
        txn_type.add_to_transcript(&mut transcript)?;

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
        txn_type: &DeviceTxnType,
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
        txn_type.add_to_transcript(&mut transcript)?;

        self.challenge_contribution(&pk_aff, &pk_enc, sk_aff_gen, sk_enc_gen, &mut transcript)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        self.verify_given_challenge(&pk_aff, &pk_enc, sk_aff_gen, sk_enc_gen, &challenge, rmc)
    }

    pub fn challenge_contribution(
        &self,
        pk_aff: &G,
        pk_enc: &G,
        sk_aff_gen: &G,
        sk_enc_gen: &G,
        transcript: &mut MerlinTranscript,
    ) -> Result<()> {
        self.proof_afk
            .challenge_contribution(sk_aff_gen, pk_aff, dst::AUTH_SK_AFF, transcript)?;

        self.proof_enc
            .challenge_contribution(sk_enc_gen, pk_enc, dst::AUTH_SK_ENC, transcript)?;
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
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        pk: &G,
        sk_gen: &G,
        transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        let proto = PokDiscreteLogProtocol::init(sk, G::ScalarField::rand(rng), sk_gen);
        proto.challenge_contribution(sk_gen, pk, dst::AUTH_SK, transcript)?;
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
        txn_type: &DeviceTxnType,
        sk_gen: &G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
        add_to_transcript!(transcript, NONCE_LABEL, nonce);
        txn_type.add_to_transcript(&mut transcript)?;
        let proto = AuthProofOnlySkProtocol::init(rng, sk, &pk, sk_gen, &mut transcript)?;
        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        Ok(proto.gen_proof(&challenge))
    }

    pub fn verify(
        &self,
        pk: G,
        nonce: &[u8],
        txn_type: &DeviceTxnType,
        sk_gen: &G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
        add_to_transcript!(transcript, NONCE_LABEL, nonce);
        txn_type.add_to_transcript(&mut transcript)?;
        self.challenge_contribution(&pk, sk_gen, &mut transcript)?;
        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        self.verify_given_challenge(&pk, sk_gen, &challenge, rmc)
    }

    pub fn challenge_contribution(
        &self,
        pk: &G,
        sk_gen: &G,
        transcript: &mut MerlinTranscript,
    ) -> Result<()> {
        self.0
            .challenge_contribution(sk_gen, pk, dst::AUTH_SK, transcript)?;
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
    use crate::Error;
    use crate::account::tests::{setup_gens_new, setup_leg_with_conf};
    use crate::account::{AccountCommitmentKeyTrait, LegProverConfig, LegVerifierConfig};
    use crate::account_registration::tests::{new_account, setup_comm_key};
    use crate::auth_proofs::account::{AuthProofAffirmation, LegAuthLink, RespAssetId};
    use crate::auth_proofs::fee_account::AuthProofFeePayment;
    use crate::auth_proofs::transparent::AuthProofTransparent;
    use crate::fee_account::tests::new_fee_account;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::leg::tests::setup_keys;
    use crate::leg::{
        LegEncConfig, PartyEphemeralPublicKey, PartyVisibility, SenderEphemeralPublicKey,
    };
    use ark_ec::CurveGroup;

    type Fr = ark_pallas::Fr;
    type PallasA = ark_pallas::Affine;

    #[test]
    fn registration() {
        // Round-trips the registration auth-proof: device proves knowledge of the signing + encryption secret keys behind the registered public keys, and the verifier accepts.
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
            &DeviceTxnType::AccountRegistration { asset_id: 1 },
            &account_comm_key.sk_gen(),
            &account_comm_key.sk_enc_gen(),
        )
        .unwrap();

        proof
            .verify(
                pk_aff.0,
                pk_enc.0,
                nonce,
                &DeviceTxnType::AccountRegistration { asset_id: 1 },
                &account_comm_key.sk_gen(),
                &account_comm_key.sk_enc_gen(),
                None,
            )
            .unwrap();

        assert!(
            proof
                .verify(
                    pk_aff.0,
                    pk_enc.0,
                    nonce,
                    &DeviceTxnType::Mint {
                        asset_id: 1,
                        amount: 10,
                    },
                    &account_comm_key.sk_gen(),
                    &account_comm_key.sk_enc_gen(),
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    pk_aff.0,
                    pk_enc.0,
                    nonce,
                    &DeviceTxnType::AccountRegistration { asset_id: 2 },
                    &account_comm_key.sk_gen(),
                    &account_comm_key.sk_enc_gen(),
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn fee_payment_auth() {
        // Round-trips the fee-payment auth-proof over the re-randomized old/updated fee-account commitments + nullifier; checks the host/device partial commitments sum to the full ones, and that a wrong nullifier/nonce/old-comm/new-comm each makes verification fail.
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2
        // const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let fee_amount = 10;

        // All parties generate their keys
        let (((sk_s, pk_s), _), (_, _), _) = setup_keys(
            &mut rng,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
        );

        let account = new_fee_account(&mut rng, asset_id, pk_s.clone(), 100);
        let account_comm = account.commit(&account_comm_key).unwrap();

        let leaf_blinding = Fr::rand(&mut rng);
        // Curve tree proof will also randomize it this way
        let re_randomized_account_commitment = (account_comm.0
            + (account_tree_params.even_parameters.pc_gens().B_blinding * leaf_blinding))
            .into_affine();

        let updated_account = account.get_state_for_payment(fee_amount).unwrap();
        let updated_account_comm = updated_account.commit(&account_comm_key).unwrap();

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
            &DeviceTxnType::FeePayment {
                asset_id,
                amount: fee_amount,
            },
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
                &DeviceTxnType::FeePayment {
                    asset_id,
                    amount: fee_amount,
                },
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

        let wrong_nullifier = PallasA::rand(&mut rng);
        assert!(
            proof
                .verify(
                    &re_randomized_account_commitment,
                    &updated_account_comm.0,
                    wrong_nullifier,
                    nonce,
                    &DeviceTxnType::FeePayment {
                        asset_id,
                        amount: fee_amount,
                    },
                    account_comm_key.sk_gen(),
                    account_comm_key.current_randomness_gen(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    &re_randomized_account_commitment,
                    &updated_account_comm.0,
                    nullifier,
                    b"wrong-nonce",
                    &DeviceTxnType::FeePayment {
                        asset_id,
                        amount: fee_amount,
                    },
                    account_comm_key.sk_gen(),
                    account_comm_key.current_randomness_gen(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                    None,
                )
                .is_err()
        );

        let wrong_re_rand = PallasA::rand(&mut rng);
        assert!(
            proof
                .verify(
                    &wrong_re_rand,
                    &updated_account_comm.0,
                    nullifier,
                    nonce,
                    &DeviceTxnType::FeePayment {
                        asset_id,
                        amount: fee_amount,
                    },
                    account_comm_key.sk_gen(),
                    account_comm_key.current_randomness_gen(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                    None,
                )
                .is_err()
        );

        let wrong_updated_comm = PallasA::rand(&mut rng);
        assert!(
            proof
                .verify(
                    &re_randomized_account_commitment,
                    &wrong_updated_comm,
                    nullifier,
                    nonce,
                    &DeviceTxnType::FeePayment {
                        asset_id,
                        amount: fee_amount,
                    },
                    account_comm_key.sk_gen(),
                    account_comm_key.current_randomness_gen(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    &re_randomized_account_commitment,
                    &updated_account_comm.0,
                    nullifier,
                    nonce,
                    &DeviceTxnType::FeePayment {
                        asset_id,
                        amount: 11,
                    },
                    account_comm_key.sk_gen(),
                    account_comm_key.current_randomness_gen(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    &re_randomized_account_commitment,
                    &updated_account_comm.0,
                    nullifier,
                    nonce,
                    &DeviceTxnType::FeePayment {
                        asset_id: 2,
                        amount: fee_amount,
                    },
                    account_comm_key.sk_gen(),
                    account_comm_key.current_randomness_gen(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    &re_randomized_account_commitment,
                    &updated_account_comm.0,
                    nullifier,
                    nonce,
                    &DeviceTxnType::FeeAccountTopup {
                        asset_id,
                        amount: fee_amount,
                    },
                    account_comm_key.sk_gen(),
                    account_comm_key.current_randomness_gen(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn transparent_auth() {
        // Round-trips the transparent (withdraw) auth-proof with two auditor keys; checks partial-commitment sums, that wrong nullifier/nonce/old-comm/new-comm fail, and that each auditor can decrypt its encrypted copy of the signing pubkey.
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let enc_key_gen = account_comm_key.sk_enc_gen();

        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let id = Fr::rand(&mut rng);

        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
        account.balance = 100;
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

        let txn_type = DeviceTxnType::Withdraw {
            asset_id,
            amount: 30,
        };

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
            &txn_type,
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
                &txn_type,
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

        // Wrong public values: verification must fail in every case because they are
        // committed into the transcript, binding the sigma responses to them.
        let wrong_nullifier = PallasA::rand(&mut rng);
        assert_err!(
            proof.verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                wrong_nullifier,
                &auditor_pubkeys,
                nonce,
                &txn_type,
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                None,
            ),
            Error::SchnorrError(_)
        );

        assert_err!(
            proof.verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                b"wrong-nonce",
                &txn_type,
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                None,
            ),
            Error::SchnorrError(_)
        );

        let wrong_re_rand = PallasA::rand(&mut rng);
        assert_err!(
            proof.verify(
                &wrong_re_rand,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                nonce,
                &txn_type,
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                None,
            ),
            Error::SchnorrError(_)
        );

        let wrong_updated_comm = PallasA::rand(&mut rng);
        assert_err!(
            proof.verify(
                &re_randomized_account_commitment,
                &wrong_updated_comm,
                nullifier,
                &auditor_pubkeys,
                nonce,
                &txn_type,
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                None,
            ),
            Error::SchnorrError(_)
        );

        assert_err!(
            proof.verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                nonce,
                &DeviceTxnType::Withdraw {
                    asset_id,
                    amount: 31,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                None,
            ),
            Error::SchnorrError(_)
        );

        assert_err!(
            proof.verify(
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                nonce,
                &DeviceTxnType::Deposit {
                    asset_id,
                    amount: 30,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                None,
            ),
            Error::SchnorrError(_)
        );

        // Verify decryption works
        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(proof.encrypted_pubkeys.decrypt(i, sk.0), pk_aff.0);
        }
    }

    #[test]
    fn affirmation_auth() {
        // Round-trips the affirmation auth-proof for the sender signing off on one leg (balance decreased); checks partial-commitment sums and that a wrong nullifier/nonce fails verification.
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

        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
        account.balance = 200;
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
            visibility: PartyVisibility::FullVisibility,
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
            amount,
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
            &DeviceTxnType::DeviceAffirmation {
                typ: DeviceAffirmationType::SenderAffirmation,
            },
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
        )
        .unwrap();

        let legs_verifier = vec![LegVerifierConfig {
            encryption: leg_enc_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
            has_balance_decreased: Some(true),
            has_counter_decreased: None,
        }];

        proof
            .verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
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

        let wrong_nullifier = PallasA::rand(&mut rng);
        assert_err!(
            proof.verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                wrong_nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::SchnorrError(_)
        );

        assert_err!(
            proof.verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                b"wrong-nonce",
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::SchnorrError(_)
        );

        let wrong_re_rand = PallasA::rand(&mut rng);
        assert_err!(
            proof.verify(
                legs_verifier.clone(),
                &wrong_re_rand,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::SchnorrError(_)
        );

        let wrong_updated_comm = PallasA::rand(&mut rng);
        assert_err!(
            proof.verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &wrong_updated_comm,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::SchnorrError(_)
        );

        let wrong_legs_verifier = vec![LegVerifierConfig {
            encryption: legs_verifier[0].encryption.clone(),
            party_eph_pk: legs_verifier[0].party_eph_pk.clone(),
            has_balance_decreased: None,
            has_counter_decreased: None,
        }];
        assert_err!(
            proof.verify(
                wrong_legs_verifier,
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::ProofVerificationError(_),
            "Invalid partial_ct_amounts length"
        );

        // Test: verifier uses a different leg encryption than what the prover used.
        // The leg encryption is added to the prover transcript, so a different encryption
        // causes the challenge to diverge and sigma responses to fail verification.
        let (_, different_leg_enc, _) = setup_leg_with_conf(
            &mut rng,
            LegEncConfig {
                visibility: PartyVisibility::FullVisibility,
                reveal_asset_id: false,
            },
            pk_enc.0,
            None,
            amount + 1, // different amount → different ciphertexts
            asset_id,
            pk_enc.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );
        let (different_leg_enc_core, different_eph_pk) =
            different_leg_enc.core_and_eph_keys_for_sender();
        let wrong_encryption_legs = vec![LegVerifierConfig {
            encryption: different_leg_enc_core,
            party_eph_pk: PartyEphemeralPublicKey::Sender(different_eph_pk),
            has_balance_decreased: Some(true),
            has_counter_decreased: None,
        }];
        assert_err!(
            proof.verify(
                wrong_encryption_legs,
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::SchnorrError(_)
        );

        let mut truncated_amount_proof = proof.clone();
        truncated_amount_proof.partial_ct_amounts.clear();
        assert_err!(
            truncated_amount_proof.verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::ProofVerificationError(_),
            "Invalid partial_ct_amounts length"
        );

        let mut truncated_asset_id_proof = proof.clone();
        truncated_asset_id_proof.partial_ct_asset_ids.clear();
        assert_err!(
            truncated_asset_id_proof.verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::ProofVerificationError(_),
            "Invalid partial_ct_asset_ids length"
        );

        // Verifier receives party_eph_pk with r4 = None while asset-id is hidden; must return Err, not panic.
        let bad_eph_pk =
            PartyEphemeralPublicKey::Sender(SenderEphemeralPublicKey { r4: None, ..eph_pk });
        let bad_legs_verifier = vec![LegVerifierConfig {
            encryption: leg_enc_core,
            party_eph_pk: bad_eph_pk,
            has_balance_decreased: Some(true),
            has_counter_decreased: None,
        }];
        assert_err!(
            proof.verify(
                bad_legs_verifier,
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::ProofVerificationError(_),
            "missing the asset-id ephemeral key"
        );

        assert_err!(
            proof.verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::ReceiverAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::SchnorrError(_)
        );

        assert_err!(
            proof.verify(
                legs_verifier.clone(),
                &re_randomized_account_commitment,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::Mint { asset_id, amount },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            ),
            Error::SchnorrError(_)
        );
    }

    #[test]
    fn affirmation_extra_amount_response_ignored() {
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
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
        account.balance = 200;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();
        let updated_account = account.get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
        let leaf_blinding = Fr::rand(&mut rng);
        let re_randomized_account_commitment =
            (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();

        let rand_part_old_comm = Fr::rand(&mut rng);
        let rand_new_comm = Fr::rand(&mut rng);
        let nullifier = PallasA::rand(&mut rng);
        let nonce = b"test-nonce";

        let conf = LegEncConfig {
            visibility: PartyVisibility::FullVisibility,
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

        let k_asset_id = Fr::rand(&mut rng);
        // Hidden asset id, no balance change -> LegAuthLink::AssetIdOnly, partial_ct_amounts empty.
        let legs_prover = vec![LegProverConfig {
            encryption: leg_enc_core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
            amount,
            has_balance_changed: false,
        }];

        let mut proof = AuthProofAffirmation::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            rand_part_old_comm,
            rand_new_comm,
            vec![],
            vec![k_asset_id],
            legs_prover,
            &re_randomized_account_commitment,
            &updated_account_comm.0,
            nullifier,
            nonce,
            &DeviceTxnType::DeviceAffirmation {
                typ: DeviceAffirmationType::SenderAffirmation,
            },
            account_comm_key.sk_gen(),
            enc_key_gen,
            b_blinding,
            enc_gen,
        )
        .unwrap();

        assert!(proof.partial_ct_amounts.is_empty());
        // Add an amount response the leg does not need; partial_ct_amounts stays empty.
        let resp_asset_id = proof.leg_links[0].resp_asset_id().unwrap().clone();
        let resp_amount = proof.resp_D.clone();
        proof.leg_links[0] = LegAuthLink::AssetIdAndAmount {
            resp_asset_id,
            resp_amount,
        };

        let legs_verifier = vec![LegVerifierConfig {
            encryption: leg_enc_core,
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
            has_balance_decreased: None,
            has_counter_decreased: None,
        }];

        assert!(
            proof
                .verify(
                    legs_verifier,
                    &re_randomized_account_commitment,
                    &updated_account_comm.0,
                    nullifier,
                    nonce,
                    &DeviceTxnType::DeviceAffirmation {
                        typ: DeviceAffirmationType::SenderAffirmation,
                    },
                    account_comm_key.sk_gen(),
                    enc_key_gen,
                    b_blinding,
                    enc_gen,
                    None,
                )
                .is_ok()
        );
    }

    #[test]
    fn affirmation_leg_link_variant_matrix() {
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
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id);
        account.balance = 200;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();
        let updated_account = account.get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
        let leaf_blinding = Fr::rand(&mut rng);
        let re_rand = (account_comm.0 + (b_blinding * leaf_blinding)).into_affine();
        let nonce = b"test-nonce";
        let nullifier = PallasA::rand(&mut rng);

        // Honest single-leg affirmation for the (reveal_asset_id, balance_changes) config.
        let build = |rng: &mut rand::rngs::ThreadRng, reveal: bool, balance: bool| {
            let (_, leg_enc, _) = setup_leg_with_conf(
                rng,
                LegEncConfig {
                    visibility: PartyVisibility::FullVisibility,
                    reveal_asset_id: reveal,
                },
                pk_enc.0,
                None,
                amount,
                asset_id,
                pk_enc.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );
            let (core, eph_pk) = leg_enc.core_and_eph_keys_for_sender();
            let needs_amount = reveal || balance;
            let k_amounts = if needs_amount {
                vec![Fr::rand(rng)]
            } else {
                vec![]
            };
            let k_asset_ids = if reveal { vec![] } else { vec![Fr::rand(rng)] };
            let rand_part_old_comm = Fr::rand(rng);
            let rand_new_comm = Fr::rand(rng);
            let proof = AuthProofAffirmation::new(
                rng,
                sk_aff.0,
                sk_enc.0,
                rand_part_old_comm,
                rand_new_comm,
                k_amounts,
                k_asset_ids,
                vec![LegProverConfig {
                    encryption: core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk.clone()),
                    amount,
                    has_balance_changed: balance,
                }],
                &re_rand,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
            )
            .unwrap();
            let verifier_leg = LegVerifierConfig {
                encryption: core,
                party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
                has_balance_decreased: if balance { Some(true) } else { None },
                has_counter_decreased: None,
            };
            (proof, verifier_leg)
        };

        let verify = |proof: &AuthProofAffirmation<PallasA>,
                      verifier_leg: &LegVerifierConfig<PallasA>| {
            proof.verify(
                vec![verifier_leg.clone()],
                &re_rand,
                &updated_account_comm.0,
                nullifier,
                nonce,
                &DeviceTxnType::DeviceAffirmation {
                    typ: DeviceAffirmationType::SenderAffirmation,
                },
                account_comm_key.sk_gen(),
                enc_key_gen,
                b_blinding,
                enc_gen,
                None,
            )
        };

        for reveal in [false, true] {
            for balance in [false, true] {
                let (proof, verifier_leg) = build(&mut rng, reveal, balance);
                let needs_amount = reveal || balance;
                let needs_asset_id = !reveal;

                assert!(
                    verify(&proof, &verifier_leg).is_ok(),
                    "honest reveal={reveal} balance={balance}"
                );

                let honest_amount = proof.leg_links[0].resp_amount().cloned();
                let honest_asset_id = proof.leg_links[0].resp_asset_id().cloned();
                let bogus_amount = proof.resp_D.clone();
                let bogus_asset_id = RespAssetId::Hidden(proof.resp_D.clone());

                if needs_amount {
                    let mut p = proof.clone();
                    p.leg_links[0] = LegAuthLink::AssetIdOnly {
                        resp_asset_id: bogus_asset_id.clone(),
                    };
                    assert!(
                        verify(&p, &verifier_leg).is_err(),
                        "dropped amount reveal={reveal} balance={balance}"
                    );
                } else {
                    let mut p = proof.clone();
                    p.leg_links[0] = LegAuthLink::AssetIdAndAmount {
                        resp_asset_id: honest_asset_id.clone().unwrap(),
                        resp_amount: bogus_amount.clone(),
                    };
                    assert!(
                        verify(&p, &verifier_leg).is_ok(),
                        "extra amount reveal={reveal} balance={balance}"
                    );
                }

                if needs_asset_id {
                    let mut p = proof.clone();
                    p.leg_links[0] = LegAuthLink::AmountOnly {
                        resp_amount: bogus_amount.clone(),
                    };
                    assert!(
                        verify(&p, &verifier_leg).is_err(),
                        "dropped asset-id reveal={reveal} balance={balance}"
                    );
                } else {
                    let mut p = proof.clone();
                    p.leg_links[0] = LegAuthLink::AssetIdAndAmount {
                        resp_asset_id: bogus_asset_id.clone(),
                        resp_amount: honest_amount.clone().unwrap(),
                    };
                    assert!(
                        verify(&p, &verifier_leg).is_ok(),
                        "extra asset-id reveal={reveal} balance={balance}"
                    );
                }
            }
        }
    }
}
