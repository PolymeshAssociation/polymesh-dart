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

    /// Insufficient commitment key length
    #[error("Commitment key length is {0} but expected at least {1}")]
    InsufficientCommitmentKeyLength(usize, usize),

    /// Expect same number of randomized points and responses for the points
    #[error("Randomized point count is {0} but expected at least {1}")]
    DifferentNumberOfRandomizedPointsAndResponses(usize, usize),

    /// Different number of responses for Sigma protocol
    #[error("Expected {0} responses for Sigma protocol but found {1}")]
    DifferentNumberOfResponsesForSigmaProtocol(usize, usize),

    /// Invalid key index
    #[error("Invalid key index {0}")]
    InvalidKeyIndex(usize),

    /// Mediator not found at index
    #[error("Expected mediator at index {0} in the keys list but it wasn't found")]
    MediatorNotFoundAtIndex(usize),

    /// Asset id mismatch between leg and asset data
    #[error("Leg asset-id is {0} but asset-data has {1}")]
    IncompatibleAssetId(AssetId, AssetId),

    /// pk_T was either provided when proof didn't have encrypted randomness or it wasn't provided when proof had encrypted randomness
    #[error("pk_T was either provided when proof didn't have encrypted randomness or it wasn't provided when proof had encrypted randomness")]
    PkTAndEncryptedRandomnessInconsistent,

    /// Can't invert 0
    #[error("Can't invert 0")]
    InvertingZero,

    /// Unexpected state size for Poseidon2
    #[error("Unexpected state size {0} for Poseidon2")]
    UnexpectedStateSizeForPoseidon2(usize),

    /// Unexpected degree for Poseidon2
    #[error("Unexpected degree {0} for Poseidon2")]
    UnexpectedDegreeForPoseidon2(usize),

    /// Full rounds must be a multiple of 2 for Poseidon2
    #[error("Full rounds must be a multiple of 2 for Poseidon2 but given as {0}")]
    IncorrectNumberOfFullRoundsForPoseidon2(usize),

    /// Input size not equal to state size
    #[error("Input size {0} not equal to state size {1}")]
    UnequalInputSizeAndStateSize(usize, usize),
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
