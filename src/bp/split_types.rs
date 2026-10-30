use ark_std::vec::Vec;
use codec::{Decode, Encode};

use polymesh_dart_bp::auth_proofs::leg::LegProverConfig as BPLegProverConfig;
use polymesh_dart_bp::auth_proofs::leg::{LegEncryptionCore, PartyEphemeralPublicKey};
use polymesh_dart_bp::auth_proofs::{
    DeviceAffirmationType as BPDeviceAffirmationType, DeviceTxnType as BPDeviceTxnType,
};
use polymesh_dart_common::{AssetId, Balance};

use super::*;
use crate::Error;

pub type BPAuthProofOnlySks = polymesh_dart_bp::auth_proofs::AuthProofOnlySks<PallasA>;
pub type BPAuthProofOnlySk = polymesh_dart_bp::auth_proofs::AuthProofOnlySk<PallasA>;

pub type BPAuthProofAffirmation =
    polymesh_dart_bp::auth_proofs::account::AuthProofAffirmation<PallasA>;
pub type BPAuthProofFeePayment =
    polymesh_dart_bp::auth_proofs::fee_account::AuthProofFeePayment<PallasA>;

#[derive(Clone, Copy, Debug, Encode, Decode, PartialEq, Eq)]
pub enum DeviceAffirmationType {
    SenderAffirmation,
    ReceiverAffirmation,
    ReceiverClaim,
    SenderReversal,
    ReceiverReversal,
    SenderCounterUpdate,
    ReceiverCounterUpdate,
    InstantSenderAffirmation,
    InstantReceiverAffirmation,
}

impl From<DeviceAffirmationType> for BPDeviceAffirmationType {
    fn from(t: DeviceAffirmationType) -> Self {
        match t {
            DeviceAffirmationType::SenderAffirmation => BPDeviceAffirmationType::SenderAffirmation,
            DeviceAffirmationType::ReceiverAffirmation => {
                BPDeviceAffirmationType::ReceiverAffirmation
            }
            DeviceAffirmationType::ReceiverClaim => BPDeviceAffirmationType::ReceiverClaim,
            DeviceAffirmationType::SenderReversal => BPDeviceAffirmationType::SenderReversal,
            DeviceAffirmationType::ReceiverReversal => BPDeviceAffirmationType::ReceiverReversal,
            DeviceAffirmationType::SenderCounterUpdate => {
                BPDeviceAffirmationType::SenderCounterUpdate
            }
            DeviceAffirmationType::ReceiverCounterUpdate => {
                BPDeviceAffirmationType::ReceiverCounterUpdate
            }
            DeviceAffirmationType::InstantSenderAffirmation => {
                BPDeviceAffirmationType::InstantSenderAffirmation
            }
            DeviceAffirmationType::InstantReceiverAffirmation => {
                BPDeviceAffirmationType::InstantReceiverAffirmation
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Encode, Decode, PartialEq, Eq)]
pub enum DeviceTxnType {
    AccountRegistration { asset_id: AssetId },
    Mint { asset_id: AssetId, amount: Balance },
    FeeAccountRegistration { asset_id: AssetId, balance: Balance },
    FeeAccountTopup { asset_id: AssetId, amount: Balance },
    FeePayment { asset_id: AssetId, amount: Balance },
    DeviceAffirmation { typ: DeviceAffirmationType },
}

impl From<DeviceTxnType> for BPDeviceTxnType {
    fn from(typ: DeviceTxnType) -> Self {
        match typ {
            DeviceTxnType::AccountRegistration { asset_id } => {
                BPDeviceTxnType::AccountRegistration { asset_id }
            }
            DeviceTxnType::Mint { asset_id, amount } => BPDeviceTxnType::Mint { asset_id, amount },
            DeviceTxnType::FeeAccountRegistration { asset_id, balance } => {
                BPDeviceTxnType::FeeAccountRegistration { asset_id, balance }
            }
            DeviceTxnType::FeeAccountTopup { asset_id, amount } => {
                BPDeviceTxnType::FeeAccountTopup { asset_id, amount }
            }
            DeviceTxnType::FeePayment { asset_id, amount } => {
                BPDeviceTxnType::FeePayment { asset_id, amount }
            }
            DeviceTxnType::DeviceAffirmation { typ } => {
                BPDeviceTxnType::DeviceAffirmation { typ: typ.into() }
            }
        }
    }
}

#[derive(Clone, Encode, Decode)]
pub struct LegProverConfig {
    encryption: WrappedCanonical<LegEncryptionCore<PallasA>>,
    party_eph_pk: WrappedCanonical<PartyEphemeralPublicKey<PallasA>>,
    amount: Balance,
    asset_id: AssetId,
    has_balance_changed: bool,
    has_counter_decreased: Option<bool>,
}

impl LegProverConfig {
    pub fn wrap(config: &BPLegProverConfig<PallasA>) -> Result<Self, Error> {
        Ok(Self {
            encryption: WrappedCanonical::wrap(&config.encryption)?,
            party_eph_pk: WrappedCanonical::wrap(&config.party_eph_pk)?,
            amount: config.amount,
            asset_id: config.asset_id,
            has_balance_changed: config.has_balance_changed,
            has_counter_decreased: config.has_counter_decreased,
        })
    }

    pub fn decode_inner(&self) -> Result<BPLegProverConfig<PallasA>, Error> {
        Ok(BPLegProverConfig {
            encryption: self.encryption.decode()?,
            party_eph_pk: self.party_eph_pk.decode()?,
            amount: self.amount,
            asset_id: self.asset_id,
            has_balance_changed: self.has_balance_changed,
            has_counter_decreased: self.has_counter_decreased,
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
    /// Opening of the new account commitment, in the order
    /// `[balance, counter, asset_id, rho, current_rho, randomness, current_randomness, id]`.
    /// The device uses it to check that the new commitment has no `comm_re_rand_gen` term.
    pub new_acc_openings: Vec<WrappedCanonical<PallasScalar>>,
    pub nullifier: CompressedAffine,
    pub k_amounts: Vec<WrappedCanonical<PallasScalar>>,
    pub k_asset_ids: Vec<WrappedCanonical<PallasScalar>>,
    pub leg_prover_configs: Vec<LegProverConfig>,
    pub txn_type: DeviceTxnType,
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
    pub txn_type: DeviceTxnType,
}

#[derive(Clone, Encode, Decode)]
pub struct RegistrationDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub pk_aff: CompressedAffine,
    pub pk_enc: CompressedAffine,
    pub txn_type: DeviceTxnType,
}

/// Mint uses the same 2-secret-key proof as registration; kept as a distinct type.
#[derive(Clone, Encode, Decode)]
pub struct MintDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub pk_aff: CompressedAffine,
    pub pk_enc: CompressedAffine,
    pub txn_type: DeviceTxnType,
}

#[derive(Clone, Encode, Decode)]
pub struct FeeAccountDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub pk: CompressedAffine,
    pub txn_type: DeviceTxnType,
}

/// Fee account registration request. The device checks `account_commitment` against the opening
/// `(initial_rho, initial_randomness)` and the balance and asset id in `txn_type`.
#[derive(Clone, Encode, Decode)]
pub struct FeeAccountRegistrationDeviceRequest {
    pub challenge_h_bytes: Vec<u8>,
    pub nonce: Vec<u8>,
    pub pk: CompressedAffine,
    pub account_commitment: CompressedAffine,
    pub initial_rho: WrappedCanonical<PallasScalar>,
    pub initial_randomness: WrappedCanonical<PallasScalar>,
    pub txn_type: DeviceTxnType,
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
