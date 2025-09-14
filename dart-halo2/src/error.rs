use thiserror::Error;
use polymesh_dart_common::{AssetId, Balance};

pub type Result<T, E = Error> = core::result::Result<T, E>;

/// The errors that can occur in the Dart protocol.
#[derive(Debug, Error)]
pub enum Error {
    /// Size mismatch error.
    #[error("Size mismatch error: difference of {0}")]
    SizeMismatch(usize),

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

    /// Sigma protocol error
    #[error("Sigma protocol error: {0}")]
    SigmaProtocolError(String),

    /// Solving discrete log failed
    #[error("Solving discrete log failed for chunk {0}")]
    SolvingDiscreteLogFailed(usize),

    /// Response for amount in leg encryption not in proof
    #[error("Response for amount in leg encryption not in proof")]
    MissingRespForLegEncAmount,
}

impl Error {
    pub fn size_mismatch(diff: usize) -> Self {
        Error::SizeMismatch(diff)
    }
}

impl From<sigma_protocols::SigmaError> for Error {
    fn from(err: sigma_protocols::SigmaError) -> Self {
        Error::SigmaProtocolError(err.to_string())
    }
}

