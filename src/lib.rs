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

pub mod init {
    use crate::{
        Error,
        curve_tree::{
            get_asset_commitment_parameters, get_pallas_layer_parameters,
            get_vesta_layer_parameters, set_asset_commitment_parameters,
            set_pallas_layer_parameters, set_vesta_layer_parameters,
        },
        dart_gens, poseidon_params, set_dart_gens, set_poseidon_params,
    };
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::vec::Vec;
    use codec::{Decode, Encode};

    pub fn init_params() -> Result<usize, Error> {
        let mut total_size = 0;
        // Generate the curve tree parameters.
        let pallas_params = get_pallas_layer_parameters();
        total_size += pallas_params.compressed_size();
        let vesta_params = get_vesta_layer_parameters();
        total_size += vesta_params.compressed_size();
        let asset_commitment_params = get_asset_commitment_parameters();
        total_size += asset_commitment_params.compressed_size();

        // Save the Dart BP parameters.
        let bp_params = dart_gens();
        total_size += bp_params.encoded_size();

        // Save the Poseidon2 parameters.
        let poseidon_2_params = poseidon_params();
        total_size += poseidon_2_params.compressed_size();

        Ok(total_size)
    }

    pub fn save_params(mut buffer: &mut Vec<u8>) -> Result<usize, Error> {
        // Save the curve tree parameters.
        let pallas_params = get_pallas_layer_parameters();
        pallas_params.serialize_compressed(&mut buffer)?;
        let vesta_params = get_vesta_layer_parameters();
        vesta_params.serialize_compressed(&mut buffer)?;
        let asset_commitment_params = get_asset_commitment_parameters();
        asset_commitment_params.serialize_compressed(&mut buffer)?;

        // Save the Dart BP parameters.
        let bp_params = dart_gens();
        bp_params.encode_to(buffer);

        // Save the Poseidon2 parameters.
        let poseidon_2_params = poseidon_params();
        poseidon_2_params.serialize_compressed(&mut buffer)?;

        Ok(buffer.len())
    }

    pub fn load_params(mut buffer: &[u8]) -> Result<(), Error> {
        // Load the curve tree parameters.
        set_pallas_layer_parameters(CanonicalDeserialize::deserialize_compressed(&mut buffer)?);
        set_vesta_layer_parameters(CanonicalDeserialize::deserialize_compressed(&mut buffer)?);
        set_asset_commitment_parameters(CanonicalDeserialize::deserialize_compressed(&mut buffer)?);

        // Load the Dart BP parameters.
        set_dart_gens(Decode::decode(&mut buffer).map_err(|_| Error::DecodeError)?);

        // Load the Poseidon2 parameters.
        set_poseidon_params(CanonicalDeserialize::deserialize_compressed(&mut buffer)?);

        Ok(())
    }
}
