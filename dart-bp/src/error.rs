use ark_std::string::String;
use thiserror::Error;

use crate::{AssetId, Balance};

pub type Result<T, E = Error> = core::result::Result<T, E>;

/// The errors that can occur in the Dart protocol.
#[derive(Debug, Error)]
pub enum Error {
    /// Curve tree error.
    #[error("Curve tree error: {0:?}")]
    CurveTreeError(#[from] curve_tree_relations::error::Error),

    /// Bulletproof r1cs error.
    #[error("Bulletproof r1cs error: {0:?}")]
    BulletproofR1CSError(#[from] bulletproofs::errors::R1CSError),

    /// Arkworks serialization error.
    #[error("Arkworks serialization error: {0}")]
    ArkworksSerializationError(ark_serialize::SerializationError),

    /// Size mismatch error.
    #[error("Size mismatch error: difference of {0}")]
    SizeMismatch(usize),

    /// Schnorr error.
    #[error("Schnorr error: {0:?}")]
    SchnorrError(schnorr_pok::error::SchnorrError),

    /// Proof of balance error.
    #[error("Proof of balance error: {0}")]
    ProofOfBalanceError(String),

    /// Invalid secret key.
    #[error("Invalid secret key: {0}")]
    InvalidSecretKey(String),

    /// Decryption failed.
    #[error("Decryption failed: {0}")]
    DecryptionFailed(String),

    /// Invalid mediator or auditor.
    #[error("Invalid mediator or auditor: {0}")]
    InvalidMediatorOrAuditor(String),

    /// Proof generation error.
    #[error("Proof generation error: {0}")]
    ProofGenerationError(String),

    /// Proof verification error.
    #[error("Proof verification error: {0}")]
    ProofVerificationError(String),

    /// Leg doesn't have a mediator.
    #[error("Leg doesn't have a mediator")]
    LegDoesNotHaveMediator,

    /// Amount is too large.
    #[error("Amount is too large: {0}")]
    AmountTooLarge(Balance),

    /// Asset ID is too large.
    #[error("Asset ID is too large: {0}")]
    AssetIdTooLarge(AssetId),

    /// Couldn't solve discrete log for chunk
    #[error("Couldn't solve discrete log for chunk index {0}")]
    SolvingDiscreteLogFailed(usize),
}

impl Error {
    pub fn size_mismatch(diff: usize) -> Self {
        Error::SizeMismatch(diff)
    }
}

impl From<ark_serialize::SerializationError> for Error {
    fn from(err: ark_serialize::SerializationError) -> Self {
        Error::ArkworksSerializationError(err)
    }
}

impl From<schnorr_pok::error::SchnorrError> for Error {
    fn from(err: schnorr_pok::error::SchnorrError) -> Self {
        Error::SchnorrError(err)
    }
}
