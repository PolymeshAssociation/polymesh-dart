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

#[cfg(feature = "host_proofs")]
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

#[cfg(feature = "host_proofs")]
pub mod init {
    use crate::{
        Error,
        curve_tree::{
            get_asset_commitment_parameters, get_pallas_layer_parameters,
            get_vesta_layer_parameters, reset_account_curve_tree_parameters,
            reset_asset_commitment_parameters, reset_asset_curve_tree_parameters,
            reset_pallas_layer_parameters, reset_vesta_layer_parameters,
            set_asset_commitment_parameters, set_pallas_layer_parameters,
            set_vesta_layer_parameters,
        },
        dart_gens, loaded_dart_gens, poseidon_params, reset_dart_gens, reset_poseidon_params,
        set_dart_gens, set_poseidon_params,
    };
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_std::vec::Vec;

    /// Checks if the parameters have been loaded.
    pub fn check_params_loaded() -> bool {
        // We just check if one of the parameters is loaded, since they are all loaded and unloaded together.
        loaded_dart_gens()
    }

    /// Initialize the parameters by generating them if they haven't already been generated.
    pub fn init_params() -> Result<usize, Error> {
        let mut total_size = 0;

        // Generate the curve tree parameters.
        let pallas_params = get_pallas_layer_parameters();
        total_size += pallas_params.uncompressed_size();
        let vesta_params = get_vesta_layer_parameters();
        total_size += vesta_params.uncompressed_size();

        // Generate the asset commitment parameters.
        let asset_commitment_params = get_asset_commitment_parameters();
        total_size += asset_commitment_params.uncompressed_size();

        // Save the Dart BP parameters.
        let bp_params = dart_gens();
        total_size += bp_params.uncompressed_size();

        // Save the Poseidon2 parameters.
        let poseidon_2_params = poseidon_params();
        total_size += poseidon_2_params.uncompressed_size();

        Ok(total_size)
    }

    /// Save the parameters to a buffer. This can be used to save the parameters to disk or to send them over the network.
    pub fn save_params(mut buffer: &mut Vec<u8>) -> Result<usize, Error> {
        // Save the curve tree parameters.
        let pallas_params = get_pallas_layer_parameters();
        pallas_params.serialize_uncompressed(&mut buffer)?;
        let vesta_params = get_vesta_layer_parameters();
        vesta_params.serialize_uncompressed(&mut buffer)?;
        let asset_commitment_params = get_asset_commitment_parameters();
        asset_commitment_params.serialize_uncompressed(&mut buffer)?;

        // Save the Dart BP parameters.
        let bp_params = dart_gens();
        bp_params.serialize_uncompressed(&mut buffer)?;

        // Save the Poseidon2 parameters.
        let poseidon_2_params = poseidon_params();
        poseidon_2_params.serialize_uncompressed(&mut buffer)?;

        Ok(buffer.len())
    }

    /// Load the parameters from a buffer. This can be used to load the parameters from disk or to receive them over the network.
    pub fn load_params(mut buffer: &[u8]) -> Result<(), Error> {
        // Load the curve tree parameters.
        set_pallas_layer_parameters(CanonicalDeserialize::deserialize_uncompressed_unchecked(
            &mut buffer,
        )?);
        set_vesta_layer_parameters(CanonicalDeserialize::deserialize_uncompressed_unchecked(
            &mut buffer,
        )?);
        set_asset_commitment_parameters(CanonicalDeserialize::deserialize_uncompressed_unchecked(
            &mut buffer,
        )?);

        // Load the Dart BP parameters.
        set_dart_gens(CanonicalDeserialize::deserialize_uncompressed_unchecked(
            &mut buffer,
        )?);

        // Load the Poseidon2 parameters.
        set_poseidon_params(CanonicalDeserialize::deserialize_uncompressed_unchecked(
            &mut buffer,
        )?);

        Ok(())
    }

    /// Unload the parameters from memory. This is mainly used for benchmarking.
    pub fn unload_params() {
        // Unload the curve tree parameters.
        reset_pallas_layer_parameters();
        reset_vesta_layer_parameters();
        reset_asset_curve_tree_parameters();
        reset_asset_commitment_parameters();
        reset_account_curve_tree_parameters();

        // Unload the Dart BP parameters.
        reset_dart_gens();

        // Unload the Poseidon2 parameters.
        reset_poseidon_params();
    }
}
