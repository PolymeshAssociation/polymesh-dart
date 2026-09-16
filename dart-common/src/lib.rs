#![cfg_attr(not(feature = "std"), no_std)]

pub type AssetId = u32;
pub type Balance = u64;
pub type PendingTxnCounter = u64;
pub type BlockNumber = u32;

pub type LegId = u8;
pub type MediatorId = u8;

pub type SkGenCounter = u16;
pub type NullifierSkGenCounter = u16;

pub const BALANCE_BITS: u16 = 48;
pub const MAX_BALANCE: u64 = (1 << BALANCE_BITS) - 1;

// 40 bits is >1M WPolyX since WPolyX has 6 decimal places. BALANCE_BITS (48) bits certainly seems high
pub const FEE_BALANCE_BITS: u16 = 40;
pub const MAX_FEE_BALANCE: u64 = (1 << FEE_BALANCE_BITS) - 1;

pub const ASSET_ID_BITS: u32 = 32;
pub const MAX_ASSET_ID: u32 = ((1_u64 << ASSET_ID_BITS) - 1) as u32;
pub const MAX_CURVE_TREE_GENS: usize = 1 << 13;
pub const MAX_ASSET_AUDITORS: u32 = 2;
pub const MAX_ASSET_MEDIATORS: u32 = 2;
/// The maximum number of encryption keys (for both auditors and mediators) that can be associated with an asset.
pub const MAX_ASSET_ENC_KEYS: u32 = MAX_ASSET_AUDITORS;
/// The maximum total number of encryption + mediator affirmation keys supported for an asset.
pub const MAX_ASSET_KEYS: u32 = MAX_ASSET_ENC_KEYS + MAX_ASSET_MEDIATORS;

pub const ACCOUNT_TREE_L: usize = 64;
pub const ACCOUNT_TREE_M: usize = 1;
pub const ACCOUNT_TREE_HEIGHT: u8 = 6;
pub const ACCOUNT_TREE_GENS: usize = MAX_CURVE_TREE_GENS;

pub const FEE_ACCOUNT_TREE_L: usize = 64;
pub const FEE_ACCOUNT_TREE_M: usize = 1;
pub const FEE_ACCOUNT_TREE_HEIGHT: u8 = 6;
pub const FEE_ACCOUNT_TREE_GENS: usize = MAX_CURVE_TREE_GENS;
pub const FEE_ASSET_ID: AssetId = 0;

pub const ASSET_TREE_L: usize = 64;
pub const ASSET_TREE_M: usize = 1;
pub const ASSET_TREE_HEIGHT: u8 = 4;
pub const ASSET_TREE_GENS: usize = MAX_CURVE_TREE_GENS;

pub const MEMO_MAX_LENGTH: u32 = 256;
pub const SETTLEMENT_MAX_LEGS: u32 = 16;

pub const MAX_KEYS_PER_REG_PROOF: u32 = 100;
pub const MAX_ACCOUNT_ASSET_REG_PROOFS: u32 = 50;
pub const MAX_BATCHED_PROOFS: u32 = 10;
pub const MAX_FEE_ACCOUNT_REG_PROOFS: u32 = 10;
pub const MAX_FEE_ACCOUNT_TOPUP_PROOFS: u32 = 10;

pub const MAX_INNER_PROOF_SIZE: u32 = 10 * 1024;

/// Pallas and Vesta points are 32 bytes when compressed. This should change if curves change
pub const COMPRESSED_POINT_SIZE: u32 = 32;

/// Maximum number of settlement creator-provided, always revealed public encryption (auditor)
/// keys in a leg.
pub const MAX_PUBLIC_ENC_KEYS: u32 = 2;

/// Upper bound on the size of a `LegEncryption`. Curve points: 4 core + 8 sender/receiver ephemeral
/// + 4 per auditor and per public key + one ephemeral per auditor key and one `ct_med` per
/// mediator. Rest 40 bytes for approx. vec lengths and option/enum tags.
pub const MAX_LEG_ENCRYPTION_SIZE: u32 = (12
    + 4 * (MAX_ASSET_ENC_KEYS + MAX_PUBLIC_ENC_KEYS)
    + MAX_ASSET_MEDIATORS * (MAX_ASSET_ENC_KEYS + 1))
    * COMPRESSED_POINT_SIZE
    + 40;

/// Upper bound on the size of a single `MediatorEncryption`: one ephemeral public key per auditor
/// key and one `ct_med`. Rest 4 bytes for the vec length.
pub const MAX_MEDIATOR_ENCRYPTION_SIZE: u32 = (MAX_ASSET_ENC_KEYS + 1) * COMPRESSED_POINT_SIZE + 4;
