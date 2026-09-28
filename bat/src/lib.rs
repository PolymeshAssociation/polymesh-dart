#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(all(feature = "ignore_prover_input_sanitation", not(debug_assertions)))]
compile_error!(
    "The feature `ignore_prover_input_sanitation` is for testing only and must not be enabled in release builds."
);

pub mod error;
pub mod hash;
pub mod protocol;
pub mod signature;

pub use error::Error;

#[cfg(feature = "bls12-381")]
pub use ark_bls12_381;
#[cfg(feature = "bn254")]
pub use ark_bn254;
