pub mod util;
pub mod old;
pub mod leg;
pub mod account_old;
pub mod account_new;
pub mod macros;

pub type AssetId = u32;
pub type Balance = u64;
pub type PendingTxnCounter = u16;

pub const AMOUNT_BITS: u16 = 48;

pub const MAX_AMOUNT: u64 = (1 << AMOUNT_BITS) - 1;

pub const MAX_ASSET_ID: u32 = ((1_u64 << 32) - 1_u64) as u32;

// TODO: The ephemeral public key created during instance should be added to the transcript.