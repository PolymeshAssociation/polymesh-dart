#![cfg_attr(not(feature = "std"), no_std)]

pub type AssetId = u32;
pub type Balance = u64;
pub type PendingTxnCounter = u64;
pub type BlockNumber = u32;

pub type SettlementId = u64;
pub type LegId = u8;
pub type MediatorId = u8;

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
pub const MAX_ASSET_KEYS: usize = (MAX_ASSET_AUDITORS + MAX_ASSET_MEDIATORS) as usize;

pub const ACCOUNT_TREE_L: usize = 512;
pub const ACCOUNT_TREE_M: usize = 1;
pub const ACCOUNT_TREE_HEIGHT: u8 = 4;
pub const ACCOUNT_TREE_GENS: usize = MAX_CURVE_TREE_GENS;

pub const ASSET_TREE_L: usize = 64;
pub const ASSET_TREE_M: usize = 1;
pub const ASSET_TREE_HEIGHT: u8 = 4;
pub const ASSET_TREE_GENS: usize = MAX_CURVE_TREE_GENS;

pub const MEMO_MAX_LENGTH: u32 = 256;
pub const SETTLEMENT_MAX_LEGS: u32 = 16;

pub const MAX_KEYS_PER_REG_PROOF: u32 = 100;
pub const MAX_ACCOUNT_ASSET_REG_PROOFS: u32 = 50;
