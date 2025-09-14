#![allow(non_snake_case)]

pub mod account;
pub mod error;
pub mod types_and_constants;
pub mod keys;
pub mod leg;
pub mod account_registration;
pub mod poseidon;
pub mod utils;
pub mod circuits;

pub use account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, PobWithAnyoneProof, PobWithAuditorProof};
pub use error::{Error, Result};
pub use keys::{keygen_enc, keygen_sig, DecKey, EncKey, SigKey, VerKey};
pub use leg::{
    EphemeralPublicKey, Leg, LegEncryption, LegEncryptionRandomness, MediatorTxnProof,
};

pub trait AffineSerializable: pasta_curves::arithmetic::CurveAffine<Scalar: ff::FromUniformBytes<64> + ff::PrimeFieldBits> + group::GroupEncoding
where
    <Self as group::prime::PrimeCurveAffine>::Scalar: ff::FromUniformBytes<64> + ff::PrimeFieldBits,
{}

impl<T> AffineSerializable for T
where
    T: pasta_curves::arithmetic::CurveAffine<Scalar: ff::FromUniformBytes<64> + ff::PrimeFieldBits> + group::GroupEncoding,
{}

// TODO: Ensure all intermediate secret values are being zeroed.

// TODO: Check this for proof aggregation https://github.com/scroll-tech/halo2-snark-aggregator