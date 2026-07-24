use thiserror::Error;

pub type Result<T, E = Error> = core::result::Result<T, E>;

/// Errors from the device wire API (SCALE/canonical (de)serialization + proof construction).
#[derive(Debug, Error)]
pub enum Error {
    /// Hex decode error.
    #[error("Hex decode error")]
    HexDecodeError,

    /// Arkworks serialization error.
    #[error("Arkworks serialization error: {0}")]
    ArkworksSerializationError(ark_serialize::SerializationError),

    /// Bounded Canonical value exceeds the specified bound.
    #[error("Bounded Canonical value exceeds the specified bound")]
    ValueExceedsBound,

    /// Auth proof error.
    #[error("Auth proof error: {0}")]
    AuthProofError(crate::Error),
}

impl From<ark_serialize::SerializationError> for Error {
    fn from(err: ark_serialize::SerializationError) -> Self {
        Error::ArkworksSerializationError(err)
    }
}

impl From<crate::Error> for Error {
    fn from(err: crate::Error) -> Self {
        Error::AuthProofError(err)
    }
}
