//! Chain errors, mirroring the Confidential Assets pallet's `Error<T>` variants
//! (`Polymesh/pallets/confidential-assets/src/lib.rs` `#[pallet::error]`).
//!
//! Keeping the variant names identical to the pallet lets tests assert that the CLI rejects the
//! same thing the pallet would, and lets `--expect-error` name a pallet error directly.

use thiserror::Error;

use polymesh_dart::Error as DartError;

#[derive(Debug, Error)]
pub enum ChainError {
    #[error("Confidential account hasn't been registered yet")]
    AccountMissing,
    #[error("Confidential account already exists")]
    AccountAlreadyCreated,
    #[error("Confidential account already registered that asset")]
    AccountAssetAlreadyRegistered,
    #[error("Encryption key already registered")]
    EncryptionKeyAlreadyRegistered,
    #[error("Confidential fee account hasn't been registered yet")]
    FeeAccountMissing,
    #[error("Confidential fee account already registered")]
    FeeAccountAlreadyRegistered,
    #[error("Invalid fee payment proof")]
    InvalidFeePaymentProof,
    #[error("Batch of proofs can't be empty")]
    EmptyBatchedProofs,
    #[error("Invalid fee asset id")]
    InvalidFeeAssetId,
    #[error("Amount overflow")]
    AmountOverflow,
    #[error("Curve tree error: {0}")]
    CurveTreeError(DartError),
    #[error("Curve tree root not found or expired")]
    CurveTreeRootNotFound,
    #[error("Leaf not found in the curve tree")]
    LeafNotFound,
    #[error("Invalid proof provided")]
    InvalidProof,
    #[error("Asset state is invalid")]
    AssetStateInvalid,
    #[error("Confidential asset hasn't been registered yet")]
    AssetMissing,
    #[error("Caller is not the owner of the Confidential account")]
    NotAccountOwner,
    #[error("Caller is not the owner of the Confidential asset")]
    NotAssetOwner,
    #[error("Asset total supply cannot exceed the maximum total supply")]
    MaxTotalSupplyExceeded,
    #[error("Nullifier for the account state commitment has already been used")]
    NullifierAlreadyUsed,
    #[error("Encryption key for the Confidential account is missing")]
    EncryptionKeyMissing,
    #[error("Settlement already exists")]
    SettlementAlreadyExists,
    #[error("Settlement is missing legs")]
    SettlementMissingLegs,
    #[error("Settlement has too many legs")]
    SettlementTooManyLegs,
    #[error("Batched settlement has invalid leg references")]
    BatchedSettlementInvalidLegRefs,
    #[error("Already affirmed")]
    AlreadyAffirmed,
    #[error("Already rejected")]
    AlreadyRejected,
    #[error("Already finalized")]
    AlreadyFinalized,
    #[error("Too many mediators for this leg")]
    TooManyMediators,
    #[error("Wrong mediator id for this leg")]
    WrongMediatorId,
    #[error("No pending affirmations for this settlement")]
    NoPendingAffirmations,
    #[error("Settlement not found")]
    SettlementNotFound,
    #[error("Leg not found in the settlement")]
    LegNotFound,
    #[error("Settlement not pending")]
    SettlementNotPending,
    #[error("Settlement not executed")]
    SettlementNotExecuted,
    #[error("Settlement has executed, cannot be reverted")]
    SettlementAlreadyExecuted,
    #[error("Curve tree parameters not set")]
    CurveTreeParametersNotSet,
    #[error("No auditors or mediators for the confidential asset")]
    NoAuditorsOrMediators,
    /// Worker session errors are runtime-harness concerns the CLI has no state for.
    #[error("No current worker session")]
    NoCurrentWorkerSession,
    #[error("Not the last pending affirmation for the settlement")]
    NotLastPendingAffirmation,
    #[error("Too many decimals for the asset")]
    TooManyDecimals,
    #[error("Name too long for the asset")]
    NameTooLong,
    #[error("Symbol too long for the asset")]
    SymbolTooLong,
    #[error("Invalid asset name")]
    InvalidAssetName,
    #[error("Invalid affirmation status transition")]
    InvalidAffirmationStatusTransition,
    #[error("Missing leg mediators")]
    MissingLegMediators,
    #[error("Encryption key does not match the registered key for the account")]
    EncryptionKeyMismatch,
    #[error("DID does not hold the required claim from a trusted issuer (or it expired)")]
    MissingRequiredClaim,
    #[error("Key distribution requires at least one recipient")]
    NoKeyRecipients,
    #[error("Too many recipients for the shared encryption key")]
    TooManySharedKeyRecipients,
    #[error("Shared encryption key has not been distributed to the mediator's key")]
    EncryptionKeyNotShared,
    #[error("A frozen asset cannot be used in a new settlement")]
    AssetIsFrozen,
    #[error("Only Root may change a Root freeze")]
    AssetFrozenByRoot,
    #[error("No more confidential asset IDs are available")]
    AssetIdOverflow,
    #[error("A registration or proof batch exceeds its runtime-configured limit")]
    TooManyProofs,
    #[error("Relayer proof submission is only permitted as the top-level call")]
    RelayerCallMustBeTopLevel,
    #[error("Leg count provided with a batched proof doesn't match the settlement")]
    SettlementLegCountMismatch,
    #[error("Insufficient balance")]
    InsufficientBalance,
    #[error("Transaction fee bounds violated (InvalidTransaction::Payment)")]
    Payment,
    #[error("Origin is not a permissioned DID")]
    BadOrigin,
}

impl ChainError {
    /// The pallet error name, for `--expect-error` and error-parity assertions.
    pub fn name(&self) -> &'static str {
        match self {
            ChainError::CurveTreeError(_) => {
                // `From<DartError> for Error<T>` maps every DART error (including root
                // misses inside proof verification) to `CurveTreeError`.
                "CurveTreeError"
            }
            other => other.variant_name(),
        }
    }

    /// Every error name this CLI can raise (parity harness input).
    pub fn all_names() -> Vec<&'static str> {
        vec![
            "AccountMissing",
            "AccountAlreadyCreated",
            "AccountAssetAlreadyRegistered",
            "EncryptionKeyAlreadyRegistered",
            "FeeAccountMissing",
            "FeeAccountAlreadyRegistered",
            "InvalidFeePaymentProof",
            "EmptyBatchedProofs",
            "InvalidFeeAssetId",
            "AmountOverflow",
            "CurveTreeError",
            "CurveTreeRootNotFound",
            "LeafNotFound",
            "InvalidProof",
            "AssetStateInvalid",
            "AssetMissing",
            "NotAccountOwner",
            "NotAssetOwner",
            "MaxTotalSupplyExceeded",
            "NullifierAlreadyUsed",
            "EncryptionKeyMissing",
            "SettlementAlreadyExists",
            "SettlementMissingLegs",
            "SettlementTooManyLegs",
            "BatchedSettlementInvalidLegRefs",
            "AlreadyAffirmed",
            "AlreadyRejected",
            "AlreadyFinalized",
            "TooManyMediators",
            "WrongMediatorId",
            "NoPendingAffirmations",
            "SettlementNotFound",
            "LegNotFound",
            "SettlementNotPending",
            "SettlementNotExecuted",
            "SettlementAlreadyExecuted",
            "CurveTreeParametersNotSet",
            "NoCurrentWorkerSession",
            "NoAuditorsOrMediators",
            "NotLastPendingAffirmation",
            "TooManyDecimals",
            "NameTooLong",
            "SymbolTooLong",
            "InvalidAssetName",
            "InvalidAffirmationStatusTransition",
            "MissingLegMediators",
            "EncryptionKeyMismatch",
            "MissingRequiredClaim",
            "NoKeyRecipients",
            "TooManySharedKeyRecipients",
            "EncryptionKeyNotShared",
            "AssetIsFrozen",
            "AssetFrozenByRoot",
            "AssetIdOverflow",
            "TooManyProofs",
            "RelayerCallMustBeTopLevel",
            "SettlementLegCountMismatch",
            "InsufficientBalance",
            "Payment",
            "BadOrigin",
        ]
    }

    fn variant_name(&self) -> &'static str {
        match self {
            ChainError::AccountMissing => "AccountMissing",
            ChainError::AccountAlreadyCreated => "AccountAlreadyCreated",
            ChainError::AccountAssetAlreadyRegistered => "AccountAssetAlreadyRegistered",
            ChainError::EncryptionKeyAlreadyRegistered => "EncryptionKeyAlreadyRegistered",
            ChainError::FeeAccountMissing => "FeeAccountMissing",
            ChainError::FeeAccountAlreadyRegistered => "FeeAccountAlreadyRegistered",
            ChainError::InvalidFeePaymentProof => "InvalidFeePaymentProof",
            ChainError::EmptyBatchedProofs => "EmptyBatchedProofs",
            ChainError::InvalidFeeAssetId => "InvalidFeeAssetId",
            ChainError::AmountOverflow => "AmountOverflow",
            ChainError::CurveTreeError(_) => "CurveTreeError",
            ChainError::CurveTreeRootNotFound => "CurveTreeRootNotFound",
            ChainError::LeafNotFound => "LeafNotFound",
            ChainError::InvalidProof => "InvalidProof",
            ChainError::AssetStateInvalid => "AssetStateInvalid",
            ChainError::AssetMissing => "AssetMissing",
            ChainError::NotAccountOwner => "NotAccountOwner",
            ChainError::NotAssetOwner => "NotAssetOwner",
            ChainError::MaxTotalSupplyExceeded => "MaxTotalSupplyExceeded",
            ChainError::NullifierAlreadyUsed => "NullifierAlreadyUsed",
            ChainError::EncryptionKeyMissing => "EncryptionKeyMissing",
            ChainError::SettlementAlreadyExists => "SettlementAlreadyExists",
            ChainError::SettlementMissingLegs => "SettlementMissingLegs",
            ChainError::SettlementTooManyLegs => "SettlementTooManyLegs",
            ChainError::BatchedSettlementInvalidLegRefs => "BatchedSettlementInvalidLegRefs",
            ChainError::AlreadyAffirmed => "AlreadyAffirmed",
            ChainError::AlreadyRejected => "AlreadyRejected",
            ChainError::AlreadyFinalized => "AlreadyFinalized",
            ChainError::TooManyMediators => "TooManyMediators",
            ChainError::WrongMediatorId => "WrongMediatorId",
            ChainError::NoPendingAffirmations => "NoPendingAffirmations",
            ChainError::SettlementNotFound => "SettlementNotFound",
            ChainError::LegNotFound => "LegNotFound",
            ChainError::SettlementNotPending => "SettlementNotPending",
            ChainError::SettlementNotExecuted => "SettlementNotExecuted",
            ChainError::SettlementAlreadyExecuted => "SettlementAlreadyExecuted",
            ChainError::CurveTreeParametersNotSet => "CurveTreeParametersNotSet",
            ChainError::NoAuditorsOrMediators => "NoAuditorsOrMediators",
            ChainError::NoCurrentWorkerSession => "NoCurrentWorkerSession",
            ChainError::NotLastPendingAffirmation => "NotLastPendingAffirmation",
            ChainError::TooManyDecimals => "TooManyDecimals",
            ChainError::NameTooLong => "NameTooLong",
            ChainError::SymbolTooLong => "SymbolTooLong",
            ChainError::InvalidAssetName => "InvalidAssetName",
            ChainError::InvalidAffirmationStatusTransition => "InvalidAffirmationStatusTransition",
            ChainError::MissingLegMediators => "MissingLegMediators",
            ChainError::EncryptionKeyMismatch => "EncryptionKeyMismatch",
            ChainError::MissingRequiredClaim => "MissingRequiredClaim",
            ChainError::NoKeyRecipients => "NoKeyRecipients",
            ChainError::TooManySharedKeyRecipients => "TooManySharedKeyRecipients",
            ChainError::EncryptionKeyNotShared => "EncryptionKeyNotShared",
            ChainError::AssetIsFrozen => "AssetIsFrozen",
            ChainError::AssetFrozenByRoot => "AssetFrozenByRoot",
            ChainError::AssetIdOverflow => "AssetIdOverflow",
            ChainError::TooManyProofs => "TooManyProofs",
            ChainError::RelayerCallMustBeTopLevel => "RelayerCallMustBeTopLevel",
            ChainError::SettlementLegCountMismatch => "SettlementLegCountMismatch",
            ChainError::InsufficientBalance => "InsufficientBalance",
            ChainError::Payment => "Payment",
            ChainError::BadOrigin => "BadOrigin",
        }
    }
}

/// `impl From<DartError> for Error<T>` in the pallet maps every DART error to `CurveTreeError`.
impl From<DartError> for ChainError {
    fn from(error: DartError) -> Self {
        ChainError::CurveTreeError(error)
    }
}

/// The pallet's `submit_and_wait` maps proof failures to `InvalidProof`, keeping the DART error as
/// context so a reviewer can see which relation failed.
pub struct ProofFailure(pub DartError);

impl std::fmt::Display for ProofFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "InvalidProof ({})", self.0)
    }
}

pub type ChainResult<T> = Result<T, ChainFailure>;

/// A chain failure.
#[derive(Debug)]
pub enum ChainFailure {
    /// A pallet error (`Error<T>::…`), the only kind a real chain dispatch can return.
    Error(ChainError),
    /// Proof verification failure: the pallet maps every `DartError` from the verifier to
    /// `Error::InvalidProof`.
    Proof(DartError),
    /// Harness plumbing (SQLite, I/O, prover-side bookkeeping). Never a dispatch outcome, so
    /// error-parity assertions ignore it.
    Internal(String),
}

impl ChainFailure {
    pub fn name(&self) -> &'static str {
        match self {
            ChainFailure::Error(e) => e.name(),
            ChainFailure::Proof(_) => "InvalidProof",
            ChainFailure::Internal(_) => "Internal",
        }
    }
}

impl From<ChainError> for ChainFailure {
    fn from(e: ChainError) -> Self {
        ChainFailure::Error(e)
    }
}

impl From<DartError> for ChainFailure {
    fn from(e: DartError) -> Self {
        ChainFailure::Proof(e)
    }
}

impl From<rusqlite::Error> for ChainFailure {
    fn from(e: rusqlite::Error) -> Self {
        ChainFailure::Internal(e.to_string())
    }
}

impl From<std::io::Error> for ChainFailure {
    fn from(e: std::io::Error) -> Self {
        ChainFailure::Internal(e.to_string())
    }
}

impl From<codec::Error> for ChainFailure {
    fn from(e: codec::Error) -> Self {
        ChainFailure::Internal(format!("scale decode error: {e}"))
    }
}

impl From<std::num::TryFromIntError> for ChainFailure {
    fn from(_: std::num::TryFromIntError) -> Self {
        ChainFailure::Error(ChainError::AmountOverflow)
    }
}

impl std::fmt::Display for ChainFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ChainFailure::Error(e) => write!(f, "{e}"),
            ChainFailure::Proof(e) => write!(f, "InvalidProof ({e})"),
            ChainFailure::Internal(e) => write!(f, "Internal ({e})"),
        }
    }
}

impl std::error::Error for ChainFailure {}
/// Parity table: every `ConfidentialAssetsError` variant of the pallet (source
/// `Polymesh/pallets/confidential-assets/src/lib.rs`, snapshot of the develop branch)
/// mapped to a same-named `ChainError` the CLI can raise. The CLI extras
/// (`InsufficientBalance`, `Payment`, `BadOrigin`) cover transaction-level failures the
/// pallet surfaces outside its own error enum.
pub const PALLET_ERROR_NAMES: &[&str] = &[
    "AccountMissing",
    "AccountAlreadyCreated",
    "AccountAssetAlreadyRegistered",
    "EncryptionKeyAlreadyRegistered",
    "FeeAccountMissing",
    "FeeAccountAlreadyRegistered",
    "InvalidFeePaymentProof",
    "EmptyBatchedProofs",
    "InvalidFeeAssetId",
    "AmountOverflow",
    "CurveTreeError",
    "CurveTreeRootNotFound",
    "LeafNotFound",
    "InvalidProof",
    "AssetStateInvalid",
    "AssetMissing",
    "NotAccountOwner",
    "NotAssetOwner",
    "MaxTotalSupplyExceeded",
    "NullifierAlreadyUsed",
    "EncryptionKeyMissing",
    "SettlementAlreadyExists",
    "SettlementMissingLegs",
    "SettlementTooManyLegs",
    "BatchedSettlementInvalidLegRefs",
    "AlreadyAffirmed",
    "AlreadyRejected",
    "AlreadyFinalized",
    "TooManyMediators",
    "WrongMediatorId",
    "NoPendingAffirmations",
    "SettlementNotFound",
    "LegNotFound",
    "SettlementNotPending",
    "SettlementNotExecuted",
    "SettlementAlreadyExecuted",
    "CurveTreeParametersNotSet",
    "NoCurrentWorkerSession",
    "NoAuditorsOrMediators",
    "NotLastPendingAffirmation",
    "TooManyDecimals",
    "NameTooLong",
    "SymbolTooLong",
    "InvalidAssetName",
    "InvalidAffirmationStatusTransition",
    "MissingLegMediators",
    "EncryptionKeyMismatch",
    "MissingRequiredClaim",
    "NoKeyRecipients",
    "TooManySharedKeyRecipients",
    "EncryptionKeyNotShared",
    "AssetIsFrozen",
    "AssetFrozenByRoot",
    "AssetIdOverflow",
    "TooManyProofs",
    "RelayerCallMustBeTopLevel",
    "SettlementLegCountMismatch",
];
