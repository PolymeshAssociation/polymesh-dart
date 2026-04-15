use ark_std::vec::Vec;
use codec::{Decode, Encode};

use polymesh_dart_bp::{
    account::common::leg_link::LegProverConfig as BPLegProverConfig,
    leg::{LegEncryptionCore, PartyEphemeralPublicKey},
};

use super::*;
use crate::Error;

pub use crate::bp::auth_proofs::{BPAuthProofOnlySk, BPAuthProofOnlySks};

pub type BPAuthProofAffirmation =
    polymesh_dart_bp::auth_proofs::account::AuthProofAffirmation<PallasA>;
pub type BPAuthProofFeePayment =
    polymesh_dart_bp::auth_proofs::fee_account::AuthProofFeePayment<PallasA>;

#[derive(Clone, Encode, Decode)]
pub struct LegProverConfig {
    encryption: WrappedCanonical<LegEncryptionCore<PallasA>>,
    party_eph_pk: WrappedCanonical<PartyEphemeralPublicKey<PallasA>>,
    has_balance_changed: bool,
}

impl LegProverConfig {
    pub fn wrap(config: &BPLegProverConfig<PallasA>) -> Result<Self, Error> {
        Ok(Self {
            encryption: WrappedCanonical::wrap(&config.encryption)?,
            party_eph_pk: WrappedCanonical::wrap(&config.party_eph_pk)?,
            has_balance_changed: config.has_balance_changed,
        })
    }

    pub fn decode_inner(&self) -> Result<BPLegProverConfig<PallasA>, Error> {
        Ok(BPLegProverConfig {
            encryption: self.encryption.decode()?,
            party_eph_pk: self.party_eph_pk.decode()?,
            has_balance_changed: self.has_balance_changed,
        })
    }
}

// DeviceRequest inner types

#[derive(Clone, Encode, Decode)]
pub struct AffirmationDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub auth_rerandomization: WrappedCanonical<PallasScalar>,
    pub auth_rand_new_comm: WrappedCanonical<PallasScalar>,
    pub rerandomized_leaf: CompressedAffine,
    pub updated_account_commitment: CompressedAffine,
    pub nullifier: CompressedAffine,
    pub k_amounts: Vec<WrappedCanonical<PallasScalar>>,
    pub k_asset_ids: Vec<WrappedCanonical<PallasScalar>>,
    pub leg_prover_configs: Vec<LegProverConfig>,
}

#[derive(Clone, Encode, Decode)]
pub struct FeePaymentDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub auth_rerandomization: WrappedCanonical<PallasScalar>,
    pub auth_new_randomness: WrappedCanonical<PallasScalar>,
    pub rerandomized_leaf: CompressedAffine,
    pub updated_account_commitment: CompressedAffine,
    pub nullifier: CompressedAffine,
}

#[derive(Clone, Encode, Decode)]
pub struct RegistrationDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub pk_aff: CompressedAffine,
    pub pk_enc: CompressedAffine,
}

#[derive(Clone, Encode, Decode)]
pub struct FeeAccountDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub pk: CompressedAffine,
}

#[derive(Clone, Encode, Decode)]
pub struct AffirmationDeviceResponse(pub WrappedCanonical<BPAuthProofAffirmation>);

#[derive(Clone, Encode, Decode)]
pub struct FeePaymentDeviceResponse(pub WrappedCanonical<BPAuthProofFeePayment>);

#[derive(Clone, Encode, Decode)]
pub struct TwoSksDeviceResponse(pub WrappedCanonical<BPAuthProofOnlySks>);

#[derive(Clone, Encode, Decode)]
pub struct SingleSkDeviceResponse(pub WrappedCanonical<BPAuthProofOnlySk>);

#[derive(Clone, Encode, Decode)]
pub struct FeeAccountPaymentDeviceResponse(pub FeePaymentDeviceResponse);

#[derive(Clone, Encode, Decode)]
pub struct AssetMintingDeviceResponse(pub TwoSksDeviceResponse);

#[derive(Clone, Encode, Decode)]
pub struct AccountRegistrationDeviceResponse(pub TwoSksDeviceResponse);

#[derive(Clone, Encode, Decode)]
pub struct FeeAccountRegistrationDeviceResponse(pub SingleSkDeviceResponse);

#[derive(Clone, Encode, Decode)]
pub struct FeeAccountTopupDeviceResponse(pub SingleSkDeviceResponse);
