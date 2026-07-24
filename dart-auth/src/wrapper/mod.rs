use ark_ec::AffineRepr;
use zeroize::{Zeroize, ZeroizeOnDrop};

pub mod encode;
pub mod error;
pub mod keys;
pub mod proofs;
pub mod types;

#[cfg(feature = "serde")]
mod serde_impl;
#[cfg(feature = "sqlx")]
mod sqlx_impl;

#[cfg(feature = "serde")]
pub use serde_impl::human_hex;

#[cfg(feature = "bounded")]
pub use encode::BoundedCanonical;
pub use encode::{
    ARK_EC_BASE_FIELD_SIZE, ARK_EC_POINT_SIZE, BaseField, CompressedAffine, CompressedBaseField,
    CompressedPoint, WrappedCanonical,
};
pub use error::Error;
pub use keys::{
    AccountPublicKey, AccountPublicKeys, AccountSecretKey, EncryptionPublicKey, EncryptionSecretKey,
};
pub use proofs::{
    create_affirmation_auth_proof, create_fee_account_auth_proof, create_fee_payment_auth_proof,
    create_registration_auth_proof,
};
pub use types::{
    AccountRegistrationDeviceResponse, AffirmationDeviceRequest, AffirmationDeviceResponse,
    AssetMintingDeviceResponse, FeeAccountDeviceRequest, FeeAccountPaymentDeviceResponse,
    FeeAccountRegistrationDeviceResponse, FeeAccountTopupDeviceResponse, FeePaymentDeviceRequest,
    FeePaymentDeviceResponse, LegProverConfig, RegistrationDeviceRequest, SingleSkDeviceResponse,
    TwoSksDeviceResponse,
};

pub type PallasA = ark_pallas::Affine;
pub type PallasScalar = <PallasA as AffineRepr>::ScalarField;

/// Device signing keys for the two-secret-key auth proofs (affirmation, transparent, mint,
/// registration). Holds only the secret scalars the device needs, not the host wallet's
/// `AccountKeys`.
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct AuthSigningKeys {
    pub sk_aff: PallasScalar,
    pub sk_enc: PallasScalar,
}

/// Device signing key for the single-secret-key auth proofs (fee registration, fee topup,
/// fee payment).
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct AuthSigningKey {
    pub sk: PallasScalar,
}
