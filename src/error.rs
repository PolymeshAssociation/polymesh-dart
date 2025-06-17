use thiserror::Error;

pub type Result<T> = core::result::Result<T, Error>;

/// The errors that can occur in the Dart protocol.
#[derive(Debug, Error)]
pub enum Error {
    /// Curve tree error.
    #[error("Curve tree error: {0:?}")]
    CurveTreeError(#[from] curve_tree_relations::error::Error),

    /// Leaf not found in the curve tree.
    #[error("Leaf not found in the curve tree: {0:?}")]
    LeafNotFound(ark_pallas::Affine),

    /// Account/Encryption public key already exists.
    #[error("Account/Encryption public key already exists.")]
    AccountPublicKeyExists,
}
