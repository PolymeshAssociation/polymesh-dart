use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum Error {
    /// A payment, issuance or key set with nothing in it.
    #[error("Nothing to issue, spend or sign")]
    Empty,
    /// Two lists that pair up element by element differ in length.
    #[error("Lists that pair up element by element differ in length")]
    LengthMismatch,
    #[error("Repeated key")]
    DuplicateKey,
    #[error("Identity point")]
    IdentityPoint,
    #[error("More tokens than fit in a u32")]
    TooManyTokens,
    /// An on-chain request that doesn't match the issuer's session.
    #[error("Request doesn't match the issuer's session")]
    SessionMismatch,
    #[error("Invalid client signature")]
    InvalidSignature,
    #[error("Invalid issuer signature")]
    InvalidIssuerSignature,
    #[error("Signature mask doesn't open the commitment")]
    InvalidSignatureMask,
}
