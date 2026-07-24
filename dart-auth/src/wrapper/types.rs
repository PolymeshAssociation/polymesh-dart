use codec::{Decode, Encode};

use super::error::Error;
use super::{CompressedAffine, PallasA, PallasScalar, WrappedCanonical};
use crate::account::AuthProofAffirmation as BPAuthProofAffirmation;
use crate::fee_account::AuthProofFeePayment as BPAuthProofFeePayment;
use crate::leg::{LegEncryptionCore, PartyEphemeralPublicKey};
use crate::leg_config::LegProverConfig as BPLegProverConfig;
use crate::{AuthProofOnlySk as BPAuthProofOnlySk, AuthProofOnlySks as BPAuthProofOnlySks};
use ark_std::vec::Vec;
use polymesh_dart_common::Balance;

#[derive(Clone, Encode, Decode)]
pub struct LegProverConfig {
    encryption: WrappedCanonical<LegEncryptionCore<PallasA>>,
    party_eph_pk: WrappedCanonical<PartyEphemeralPublicKey<PallasA>>,
    amount: Balance,
    has_balance_changed: bool,
}

impl LegProverConfig {
    pub fn wrap(config: &BPLegProverConfig<PallasA>) -> Result<Self, Error> {
        Ok(Self {
            encryption: WrappedCanonical::wrap(&config.encryption)?,
            party_eph_pk: WrappedCanonical::wrap(&config.party_eph_pk)?,
            amount: config.amount,
            has_balance_changed: config.has_balance_changed,
        })
    }

    pub fn decode_inner(&self) -> Result<BPLegProverConfig<PallasA>, Error> {
        Ok(BPLegProverConfig {
            encryption: self.encryption.decode()?,
            party_eph_pk: self.party_eph_pk.decode()?,
            amount: self.amount,
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
pub struct AffirmationDeviceResponse(pub WrappedCanonical<BPAuthProofAffirmation<PallasA>>);

#[derive(Clone, Encode, Decode)]
pub struct FeePaymentDeviceResponse(pub WrappedCanonical<BPAuthProofFeePayment<PallasA>>);

#[derive(Clone, Encode, Decode)]
pub struct TwoSksDeviceResponse(pub WrappedCanonical<BPAuthProofOnlySks<PallasA>>);

#[derive(Clone, Encode, Decode)]
pub struct SingleSkDeviceResponse(pub WrappedCanonical<BPAuthProofOnlySk<PallasA>>);

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
