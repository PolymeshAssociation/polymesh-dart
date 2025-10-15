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
    ACCOUNT_TREE_GENS, ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_L, ACCOUNT_TREE_M, ASSET_TREE_GENS,
    ASSET_TREE_HEIGHT, ASSET_TREE_L, ASSET_TREE_M, AssetId, BALANCE_BITS, Balance, BlockNumber,
    FEE_ACCOUNT_TREE_GENS, FEE_ACCOUNT_TREE_HEIGHT, FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M,
    FEE_BALANCE_BITS, LegId, MAX_ASSET_ID, MAX_BALANCE, MAX_CURVE_TREE_GENS, MediatorId,
    PendingTxnCounter, SettlementId,
};

#[cfg(feature = "sp-io")]
pub fn blake2_256<T: codec::Encode>(data: &T) -> [u8; 32] {
    data.using_encoded(sp_io::hashing::blake2_256)
}

#[cfg(not(feature = "sp-io"))]
pub fn blake2_256<T: codec::Encode>(data: &T) -> [u8; 32] {
    use blake2::{Blake2s256, Digest};
    let mut hasher = Blake2s256::new();
    hasher.update(&data.encode());
    hasher.finalize().into()
}
