//! BAT fee tokens (<https://eprint.iacr.org/2026/1074>, Protocol A) over `polymesh-bat`, with the
//! curves fixed and the on-chain messages SCALE encoded.
//!
//! Chain state (issuer registry, escrow, sessions, nullifiers, counters) is the pallet's. The
//! verification functions here take what the pallet looked up and return what it must record.

use ark_ec::{AffineRepr, pairing::Pairing};

use crate::*;

mod encode;
pub use encode::*;

mod messages;
pub use messages::*;

mod client;
pub use client::*;

mod issuer;
pub use issuer::*;

mod fee;
pub use fee::*;

pub type BatPairing = polymesh_bat::ark_bn254::Bn254;
pub type BatScalar = <BatPairing as Pairing>::ScalarField;
pub type BatG1 = <BatPairing as Pairing>::G1Affine;
pub type BatG2 = <BatPairing as Pairing>::G2Affine;

/// Compressed sizes of `G1` and `G2` of the pairing curve. This should change when the pairing curve
/// changes.
pub const BAT_G1_SIZE: usize = 32;
pub const BAT_G2_SIZE: usize = 64;

/// Index of an issuer key in the pallet's registry. Each key has one denomination.
pub type BatIssuerKeyId = u32;

pub type BatSessionId = [u8; 32];

pub const MAX_BAT_TOKENS_PER_PAYMENT: u32 = 64;
pub const MAX_BAT_ISSUER_KEYS_PER_PAYMENT: u32 = 32;
pub const MAX_BAT_TOKENS_PER_SESSION: u32 = 256;

/// Base of the client signature scheme.
pub fn bat_signature_base() -> PallasA {
    PallasA::generator()
}

pub trait BatLimits: DartLimits {
    /// The maximum number of tokens in a payment.
    type MaxBatTokensPerPayment: GetExtra<u32>;

    /// The maximum number of distinct issuer keys in a payment.
    type MaxBatIssuerKeysPerPayment: GetExtra<u32>;

    /// The maximum number of tokens bought in one session, which also bounds a refund.
    type MaxBatTokensPerSession: GetExtra<u32>;
}

impl BatLimits for () {
    type MaxBatTokensPerPayment = ConstSize<MAX_BAT_TOKENS_PER_PAYMENT>;
    type MaxBatIssuerKeysPerPayment = ConstSize<MAX_BAT_ISSUER_KEYS_PER_PAYMENT>;
    type MaxBatTokensPerSession = ConstSize<MAX_BAT_TOKENS_PER_SESSION>;
}

impl BatLimits for PolymeshLimits {
    type MaxBatTokensPerPayment = ConstSize<MAX_BAT_TOKENS_PER_PAYMENT>;
    type MaxBatIssuerKeysPerPayment = ConstSize<MAX_BAT_ISSUER_KEYS_PER_PAYMENT>;
    type MaxBatTokensPerSession = ConstSize<MAX_BAT_TOKENS_PER_SESSION>;
}
