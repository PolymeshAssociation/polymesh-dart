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
    FEE_ASSET_ID, FEE_BALANCE_BITS, LegId, MAX_ASSET_ID, MAX_BALANCE, MAX_CURVE_TREE_GENS,
    MediatorId, PendingTxnCounter,
};

#[cfg(feature = "sp-io")]
pub fn blake2_256<T: codec::Encode>(data: &T) -> [u8; 32] {
    data.using_encoded(sp_io::hashing::blake2_256)
}

#[cfg(not(feature = "sp-io"))]
pub fn blake2_256<T: codec::Encode>(data: &T) -> [u8; 32] {
    use digest::{Digest, generic_array::typenum::U32};
    type Blake2b256 = blake2::Blake2b<U32>;
    Blake2b256::digest(&data.encode()).into()
}
