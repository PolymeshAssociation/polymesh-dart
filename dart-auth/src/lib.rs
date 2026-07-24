#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]
#![cfg_attr(feature = "nightly_mocking_tests", feature(proc_macro_hygiene))]

#[macro_use]
mod macros;

pub mod account;
pub mod error;
pub mod fee_account;
pub mod helpers;
pub mod keys;
pub mod leg;
pub mod leg_config;
pub mod transparent;

#[cfg(feature = "wrapper")]
pub mod wrapper;

pub use error::Error;

use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::io::Write;
use ark_std::vec::Vec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use error::Result;
use polymesh_dart_common::{NONCE_LABEL, PK_ENC_LABEL, PK_LABEL, TXN_CHALLENGE_LABEL};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol};

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
