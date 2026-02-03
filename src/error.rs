use thiserror::Error;

use polymesh_dart_common::AssetId;

use crate::{ChildIndex, LeafIndex, NodeIndex, NodeLevel};
use ark_std::string::String;

/// The errors that can occur in the Dart protocol.
#[derive(Debug, Error)]
pub enum Error {
    /// DART Bulletproofs error.
    #[error("DART Bulletproofs error: {0}")]
    DartBulletproofsError(#[from] polymesh_dart_bp::Error),

    /// Curve tree error.
    #[error("Curve tree error: {0:?}")]
    CurveTreeError(#[from] curve_tree_relations::error::Error),

    /// Leaf not found in the curve tree.
    #[error("Leaf not found in the curve tree")]
    LeafNotFound,

    /// Leaf index not found in the curve tree.
    #[error("Leaf index not found in the curve tree: {0}")]
    LeafIndexNotFound(LeafIndex),

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
    CurveTreeLeafIndexOutOfBounds(LeafIndex),

    /// Curve tree invalid child index.
    #[error("Curve tree invalid child index: {0}")]
    CurveTreeInvalidChildIndex(ChildIndex),

    /// Curve tree leaf cannot have children.
    #[error("Curve tree leaf cannot have children.")]
    CurveTreeLeafCannotHaveChildren,

    /// Curve tree invalid child node.
    #[error("Curve tree invalid child node at level {level}, index {index}")]
    CurveTreeInvalidChildNode { level: NodeLevel, index: NodeIndex },

    /// Curve tree node not found at a specific level and index.
    #[error("Curve tree node not found at level {level}, index {index}")]
    CurveTreeNodeNotFound { level: NodeLevel, index: NodeIndex },

    /// Curve tree generator not found.
    #[error("Curve tree generator not found.")]
    CurveTreeGeneratorNotFound,

    /// Curve tree cannot update a leaf in an append-only tree.
    #[error("Curve tree cannot update a leaf in an append-only tree.")]
    CurveTreeCannotUpdateLeafInAppendOnlyTree,

    /// Asset state not found.
    #[error("Asset state not found: {0:?}")]
    AssetStateNotFound(AssetId),

    /// Arkworks serialization error.
    #[error("Arkworks serialization error: {0}")]
    ArkworksSerializationError(ark_serialize::SerializationError),

    /// Curve tree block number not found.
    #[error("Curve tree block number not found.")]
    CurveTreeBlockNumberNotFound,

    /// Curve tree backend is read-only.
    #[error("Curve tree backend is read-only.")]
    CurveTreeBackendReadOnly,

    /// Curve tree update error.
    #[error("Curve tree update error.")]
    CurveTreeUpdateError,

    /// Leg decryption error.
    #[error("Leg decryption error: {0}")]
    LegDecryptionError(String),

    /// Hex decode error.
    #[error("Hex decode error")]
    HexDecodeError,

    /// Too many keys in registration proof.
    #[error("Too many keys in registration proof")]
    TooManyKeysInRegProof,

    /// Too many account asset registration proofs in transaction.
    #[error("Too many account asset registration proofs in transaction")]
    TooManyAccountAssetRegProofs,

    /// Too many proofs in batched proof.
    #[error("Too many proofs in batched proof")]
    TooManyBatchedProofs,

    /// RMC failed to verify.
    #[error("RMC failed to verify")]
    RMCVerifyError,
}

impl From<ark_serialize::SerializationError> for Error {
    fn from(err: ark_serialize::SerializationError) -> Self {
        Error::ArkworksSerializationError(err)
    }
}
