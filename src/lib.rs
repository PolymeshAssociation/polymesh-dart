#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "backend_bp")]
mod bp;
#[cfg(feature = "backend_bp")]
pub use bp::*;

#[cfg(feature = "serde")]
mod serde_impl;
#[cfg(feature = "serde")]
pub use serde_impl::*;

mod error;
pub use error::Error;

pub mod curve_tree;

pub use polymesh_dart_common::{
    ACCOUNT_TREE_GENS, ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_L, ACCOUNT_TREE_M, BALANCE_BITS,
    ASSET_TREE_GENS, ASSET_TREE_HEIGHT, ASSET_TREE_L, ASSET_TREE_M, AssetId, Balance, BlockNumber,
    LegId, MAX_BALANCE, MAX_ASSET_ID, MAX_CURVE_TREE_GENS, MediatorId, PendingTxnCounter,
    SettlementId,
};
