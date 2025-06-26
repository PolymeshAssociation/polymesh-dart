use thiserror::Error;

use dart_common::AssetId;

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

    /// Bounded container size limit exceeded.
    #[error("Bounded container size limit exceeded.")]
    BoundedContainerSizeLimitExceeded,

    /// Bulletproof r1cs error.
    #[error("Bulletproof r1cs error: {0:?}")]
    BulletproofR1CSError(#[from] bulletproofs::errors::R1CSError),

    /// Curve tree root not found.
    #[error("Curve tree root not found.")]
    CurveTreeRootNotFound,

    /// Curve tree leaf index is out of bounds.
    #[error("Curve tree leaf index is out of bounds: {0}")]
    CurveTreeLeafIndexOutOfBounds(usize),

    /// Curve tree invalid child index.
    #[error("Curve tree invalid child index: {0}")]
    CurveTreeInvalidChildIndex(usize),

    /// Curve tree leaf cannot have children.
    #[error("Curve tree leaf cannot have children.")]
    CurveTreeLeafCannotHaveChildren,

    /// Curve tree invalid child node.
    #[error("Curve tree invalid child node at level {level}, index {index}")]
    CurveTreeInvalidChildNode { level: usize, index: usize },

    /// Curve tree node not found at a specific level and index.
    #[error("Curve tree node not found at level {level}, index {index}")]
    CurveTreeNodeNotFound { level: usize, index: usize },

    /// Curve tree backend error.
    #[error("Curve tree backend error: {0:?}")]
    CurveTreeBackendError(Box<dyn std::error::Error + Send + Sync>),

    /// Curve tree generator not found.
    #[error("Curve tree generator not found.")]
    CurveTreeGeneratorNotFound,

    /// Asset state not found.
    #[error("Asset state not found: {0:?}")]
    AssetStateNotFound(AssetId),
}
