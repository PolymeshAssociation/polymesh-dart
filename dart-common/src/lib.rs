pub type AssetId = u32;
pub type Balance = u64;
pub type PendingTxnCounter = u16;

pub const AMOUNT_BITS: u16 = 48;

pub const MAX_AMOUNT: u64 = (1 << AMOUNT_BITS) - 1;

pub const MAX_ASSET_ID: u32 = u32::MAX;

pub const ACCOUNT_TREE_L: usize = 512;
pub const ACCOUNT_TREE_HEIGHT: u8 = 4;
pub const ACCOUNT_TREE_GENS: usize = 1 << 12;

pub const ASSET_TREE_L: usize = 64;
pub const ASSET_TREE_HEIGHT: u8 = 4;
pub const ASSET_TREE_GENS: usize = 1 << 13;
