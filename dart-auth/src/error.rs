use ark_std::string::String;
use thiserror::Error;

pub type Result<T, E = Error> = core::result::Result<T, E>;

/// The errors that can occur in the auth proofs.
#[derive(Debug, Error)]
pub enum Error {
    /// Arkworks serialization error.
    #[error("Arkworks serialization error: {0}")]
    ArkworksSerializationError(ark_serialize::SerializationError),

    /// Schnorr error.
    #[error("Schnorr error: {0:?}")]
    SchnorrError(schnorr_pok::error::SchnorrError),

    /// Proof generation error.
    #[error("Proof generation error: {0}")]
    ProofGenerationError(String),

    /// Proof verification error.
    #[error("Proof verification error: {0}")]
    ProofVerificationError(String),

    /// Different number of responses for Sigma protocol
    #[error("Expected {0} responses for Sigma protocol but found {1}")]
    DifferentNumberOfResponsesForSigmaProtocol(usize, usize),

    /// Can't invert 0
    #[error("Can't invert 0")]
    InvertingZero,

    /// Different number of encryptions or proofs for auditor keys
    #[error("Expected {0} but found {1}")]
    EncryptionOrProofsNotPresentForAllKeys(usize, usize),

    /// Point at identity not allowed
    #[error("Point at identity not allowed")]
    PointAtIdentity,
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
