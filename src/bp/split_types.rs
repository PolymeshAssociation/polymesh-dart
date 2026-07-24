use super::*;

pub use crate::bp::auth_proofs::{BPAuthProofOnlySk, BPAuthProofOnlySks};

pub use polymesh_dart_auth::wrapper::{
    AccountRegistrationDeviceResponse, AffirmationDeviceRequest, AffirmationDeviceResponse,
    AssetMintingDeviceResponse, FeeAccountDeviceRequest, FeeAccountPaymentDeviceResponse,
    FeeAccountRegistrationDeviceResponse, FeeAccountTopupDeviceResponse, FeePaymentDeviceRequest,
    FeePaymentDeviceResponse, LegProverConfig, RegistrationDeviceRequest, SingleSkDeviceResponse,
    TwoSksDeviceResponse,
};

pub type BPAuthProofAffirmation =
    polymesh_dart_bp::auth_proofs::account::AuthProofAffirmation<PallasA>;
pub type BPAuthProofFeePayment =
    polymesh_dart_bp::auth_proofs::fee_account::AuthProofFeePayment<PallasA>;
