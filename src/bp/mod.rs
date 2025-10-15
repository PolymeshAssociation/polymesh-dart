use codec::{Decode, Encode};

use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::{
    PrimeField,
    field_hashers::{DefaultFieldHasher, HashToField},
};
use ark_serialize::CanonicalSerialize;

use blake2::Blake2b512;
use bounded_collections::{ConstU32, Get};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use digest::Digest;

use polymesh_dart_bp::{
    account::AccountCommitmentKeyTrait,
    poseidon_impls::poseidon_2::{
        Poseidon2Params, params::pallas::get_poseidon2_params_for_2_1_hashing,
    },
};
use polymesh_dart_common::{
    MAX_ACCOUNT_ASSET_REG_PROOFS, MAX_ASSET_AUDITORS, MAX_ASSET_MEDIATORS, MAX_KEYS_PER_REG_PROOF,
    MEMO_MAX_LENGTH, SETTLEMENT_MAX_LEGS,
};

#[cfg(feature = "sqlx")]
pub mod sqlx_impl;

pub mod encode;
pub use encode::{CompressedAffine, WrappedCanonical};

mod asset;
pub use asset::*;

mod account;
pub use account::*;

mod leg;
pub use leg::*;

mod keys;
pub use keys::*;

mod fee;
pub use fee::*;

use crate::curve_tree::{
    CompressedLeafValue, CurveTreeConfig, CurveTreeLookup, CurveTreePath, FeeAccountTreeConfig,
    ValidateCurveTreeRoot,
};
use crate::*;

pub trait DartLimits: Clone + core::fmt::Debug {
    /// The maximum number of keys in an account registration proof.
    type MaxKeysPerRegProof: Get<u32> + Clone + core::fmt::Debug;

    /// The maximum number of account asset registration proofs in a single transaction.
    type MaxAccountAssetRegProofs: Get<u32> + Clone + core::fmt::Debug;

    /// The maximum number of legs in a settlement.
    type MaxSettlementLegs: Get<u32> + Clone + core::fmt::Debug;

    /// The maximum settlement memo length.
    type MaxSettlementMemoLength: Get<u32> + Clone + core::fmt::Debug;

    /// The maximum number of asset auditors.
    type MaxAssetAuditors: Get<u32> + Clone + core::fmt::Debug;

    /// The maximum number of asset mediators.
    type MaxAssetMediators: Get<u32> + Clone + core::fmt::Debug;
}

impl DartLimits for () {
    type MaxKeysPerRegProof = ConstU32<500>;
    type MaxAccountAssetRegProofs = ConstU32<200>;
    type MaxSettlementLegs = ConstU32<SETTLEMENT_MAX_LEGS>;
    type MaxSettlementMemoLength = ConstU32<MEMO_MAX_LENGTH>;
    type MaxAssetAuditors = ConstU32<MAX_ASSET_AUDITORS>;
    type MaxAssetMediators = ConstU32<MAX_ASSET_MEDIATORS>;
}

#[derive(Clone, Copy, Debug)]
pub struct PolymeshPrivateLimits;

impl DartLimits for PolymeshPrivateLimits {
    type MaxKeysPerRegProof = ConstU32<MAX_KEYS_PER_REG_PROOF>;
    type MaxAccountAssetRegProofs = ConstU32<MAX_ACCOUNT_ASSET_REG_PROOFS>;
    type MaxSettlementLegs = ConstU32<SETTLEMENT_MAX_LEGS>;
    type MaxSettlementMemoLength = ConstU32<MEMO_MAX_LENGTH>;
    type MaxAssetAuditors = ConstU32<MAX_ASSET_AUDITORS>;
    type MaxAssetMediators = ConstU32<MAX_ASSET_MEDIATORS>;
}

pub type LeafIndex = u64;
pub type TreeIndex = u8;
pub type NodeLevel = u8;
pub type NodeIndex = LeafIndex;
pub type ChildIndex = LeafIndex;

pub type PallasParameters = ark_pallas::PallasConfig;
pub type VestaParameters = ark_vesta::VestaConfig;
pub type PallasA = ark_pallas::Affine;
pub type PallasScalar = <PallasA as AffineRepr>::ScalarField;
pub type VestaA = ark_vesta::Affine;
pub type VestaScalar = <VestaA as AffineRepr>::ScalarField;

pub const ACCOUNT_IDENTITY_LABEL: &[u8; 16] = b"account-identity";
pub(crate) fn hash_identity<F: PrimeField>(did: &[u8]) -> F {
    let hasher = <DefaultFieldHasher<Blake2b512> as HashToField<F>>::new(ACCOUNT_IDENTITY_LABEL);
    let r = hasher.hash_to_field(&did, 1);
    r[0]
}

/// Constants that are hashed to generate the generators for the Dart BP protocol.
pub const DART_GEN_DOMAIN: &'static [u8] = b"polymesh-dart-generators";
pub const DART_GEN_ACCOUNT_KEY: &'static [u8] = b"polymesh-dart-account-key";
pub const DART_GEN_ASSET_KEY: &'static [u8] = b"polymesh-dart-asset-key";
pub const DART_GEN_ENC_KEY: &'static [u8] = b"polymesh-dart-pk-enc";

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    pub static ref DART_GENS: DartBPGenerators = DartBPGenerators::new(DART_GEN_DOMAIN);

    pub static ref POSEIDON_PARAMS: PoseidonParameters = PoseidonParameters::new().expect("Failed to create Poseidon parameters");
}

#[cfg(feature = "std")]
pub fn dart_gens() -> &'static DartBPGenerators {
    &DART_GENS
}

#[cfg(not(feature = "std"))]
static mut DART_GENS: Option<DartBPGenerators> = None;

#[cfg(not(feature = "std"))]
#[allow(static_mut_refs)]
pub fn dart_gens() -> &'static DartBPGenerators {
    unsafe {
        if DART_GENS.is_none() {
            DART_GENS = Some(DartBPGenerators::new(DART_GEN_DOMAIN));
        }
        DART_GENS.as_ref().unwrap()
    }
}

#[cfg(feature = "std")]
pub fn poseidon_params() -> &'static PoseidonParameters {
    &POSEIDON_PARAMS
}

#[cfg(not(feature = "std"))]
static mut POSEIDON_PARAMS: Option<PoseidonParameters> = None;

#[cfg(not(feature = "std"))]
#[allow(static_mut_refs)]
pub fn poseidon_params() -> &'static PoseidonParameters {
    unsafe {
        if POSEIDON_PARAMS.is_none() {
            POSEIDON_PARAMS =
                Some(PoseidonParameters::new().expect("Failed to create Poseidon parameters"));
        }
        POSEIDON_PARAMS.as_ref().unwrap()
    }
}

pub struct PoseidonParameters {
    pub params: Poseidon2Params<PallasScalar>,
}

impl PoseidonParameters {
    pub fn new() -> Result<Self, Error> {
        Ok(Self {
            params: get_poseidon2_params_for_2_1_hashing()?,
        })
    }
}

#[derive(Clone, Copy, Debug, Encode, Decode, PartialEq, Eq, CanonicalSerialize)]
pub struct AccountCommitmentKey {
    #[codec(encoded_as = "CompressedAffine")]
    pub sk_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub balance_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub counter_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub asset_id_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub rho_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub current_rho_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub randomness_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub identity_gen: PallasA,
}

impl AccountCommitmentKey {
    /// Create a new account commitment key
    pub fn new<D: Digest>(label: &[u8], sk_gen: PallasA) -> Self {
        let balance_gen = hash_to_pallas(label, b" : balance_gen").into_affine();
        let counter_gen = hash_to_pallas(label, b" : counter_gen").into_affine();
        let asset_id_gen = hash_to_pallas(label, b" : asset_id_gen").into_affine();
        let rho_gen = hash_to_pallas(label, b" : rho_gen").into_affine();
        let current_rho_gen = hash_to_pallas(label, b" : current_rho_gen").into_affine();
        let randomness_gen = hash_to_pallas(label, b" : randomness_gen").into_affine();
        let identity_gen = hash_to_pallas(label, b" : identity_gen").into_affine();

        Self {
            sk_gen,
            balance_gen,
            counter_gen,
            asset_id_gen,
            rho_gen,
            current_rho_gen,
            randomness_gen,
            identity_gen,
        }
    }
}

impl AccountCommitmentKeyTrait<PallasA> for AccountCommitmentKey {
    fn sk_gen(&self) -> PallasA {
        self.sk_gen
    }

    fn balance_gen(&self) -> PallasA {
        self.balance_gen
    }

    fn counter_gen(&self) -> PallasA {
        self.counter_gen
    }

    fn asset_id_gen(&self) -> PallasA {
        self.asset_id_gen
    }

    fn rho_gen(&self) -> PallasA {
        self.rho_gen
    }

    fn current_rho_gen(&self) -> PallasA {
        self.current_rho_gen
    }

    fn randomness_gen(&self) -> PallasA {
        self.randomness_gen
    }

    fn id_gen(&self) -> PallasA {
        self.identity_gen
    }
}

/// The generators for the Dart BP protocol.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq)]
pub struct DartBPGenerators {
    #[codec(encoded_as = "CompressedAffine")]
    sig_key_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    enc_key_gen: PallasA,
    account_comm_key: AccountCommitmentKey,
    #[codec(encoded_as = "CompressedAffine")]
    leg_asset_value_gen: PallasA,
}

impl DartBPGenerators {
    /// Creates a new instance of `DartBPGenerators` by generating the necessary generators.
    pub fn new(label: &[u8]) -> Self {
        let sig_key_gen = hash_to_pallas(label, b" : sig_key_gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b" : enc_key_gen").into_affine();

        let account_comm_key =
            AccountCommitmentKey::new::<Blake2b512>(DART_GEN_ACCOUNT_KEY, sig_key_gen);

        let leg_asset_value_gen = hash_to_pallas(label, b" : leg_asset_value_gen").into_affine();

        Self {
            sig_key_gen,
            enc_key_gen,
            account_comm_key,
            leg_asset_value_gen,
        }
    }

    /// Returns the generators for account state commitments.
    pub fn account_comm_key(&self) -> AccountCommitmentKey {
        self.account_comm_key
    }

    pub fn sig_key_gen(&self) -> PallasA {
        self.sig_key_gen
    }

    pub fn enc_key_gen(&self) -> PallasA {
        self.enc_key_gen
    }

    pub fn leg_asset_value_gen(&self) -> PallasA {
        self.leg_asset_value_gen
    }
}

pub(crate) fn try_block_number<T: TryInto<BlockNumber>>(
    block_number: T,
) -> Result<BlockNumber, Error> {
    block_number
        .try_into()
        .map_err(|_| Error::CurveTreeBlockNumberNotFound)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Test encode/decode of DartBPGenerators.
    #[test]
    fn test_dart_bp_generators_encode_decode() {
        let gens = dart_gens().clone();

        let encoded = gens.encode();
        let decoded: DartBPGenerators = Decode::decode(&mut &encoded[..]).unwrap();
        assert_eq!(gens, decoded);
    }
}
