use core::marker::PhantomData;
#[cfg(feature = "std")]
use std::collections::HashMap;

use ark_ff::{
    PrimeField,
    field_hashers::{DefaultFieldHasher, HashToField},
};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, Encode, MaxEncodedLen};
use curve_tree_relations::curve_tree::Root;
use dock_crypto_utils::concat_slices;
use dock_crypto_utils::hashing_utils::affine_group_elem_from_try_and_incr;
use polymesh_dart_bp::account::AccountCommitmentKeyTrait;
use scale_info::TypeInfo;

use ark_ec::{AffineRepr, CurveConfig};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    format,
    string::{String, ToString},
    vec::Vec,
};
use blake2::{Blake2b512, Blake2s256};
use rand_core::{CryptoRng, RngCore, SeedableRng as _};

use bounded_collections::{BoundedBTreeSet, BoundedVec, ConstU32, Get};

use digest::Digest;
use polymesh_dart_bp::{
    account as bp_account, account_registration, keys as bp_keys, leg as bp_leg,
};
use polymesh_dart_common::{
    LegId, MAX_ASSET_AUDITORS, MAX_ASSET_MEDIATORS, MEMO_MAX_LENGTH, MediatorId,
    NullifierSkGenCounter, SETTLEMENT_MAX_LEGS, SettlementId,
};

use polymesh_dart_bp::poseidon_impls::poseidon_2::Poseidon2Params;

#[cfg(feature = "sqlx")]
pub mod sqlx_impl;

pub mod encode;
pub use encode::{CompressedAffine, WrappedCanonical};
use zeroize::{Zeroize, ZeroizeOnDrop};

use crate::curve_tree::*;
use crate::*;

pub trait DartLimits: Clone + core::fmt::Debug {
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
    type MaxSettlementLegs = ConstU32<SETTLEMENT_MAX_LEGS>;
    type MaxSettlementMemoLength = ConstU32<MEMO_MAX_LENGTH>;
    type MaxAssetAuditors = ConstU32<MAX_ASSET_AUDITORS>;
    type MaxAssetMediators = ConstU32<MAX_ASSET_MEDIATORS>;
}

#[derive(Clone, Copy, Debug)]
pub struct PolymeshPrivateLimits;

impl DartLimits for PolymeshPrivateLimits {
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

type BPAccountState = bp_account::AccountState<PallasA>;
type BPAccountStateCommitment = bp_account::AccountStateCommitment<PallasA>;

pub type AssetCommitmentData =
    bp_leg::AssetData<PallasScalar, VestaScalar, PallasParameters, VestaParameters>;

pub const ACCOUNT_IDENTITY_LABEL: &[u8; 16] = b"account-identity";
fn hash_identity<F: PrimeField>(did: &[u8]) -> F {
    let hasher = <DefaultFieldHasher<Blake2b512> as HashToField<F>>::new(ACCOUNT_IDENTITY_LABEL);
    let r = hasher.hash_to_field(&did, 1);
    r[0]
}

/// Constants that are hashed to generate the generators for the Dart BP protocol.
pub const DART_GEN_DOMAIN: &'static [u8] = b"polymesh-dart-generators";
pub const DART_GEN_ACCOUNT_KEY: &'static [u8] = b"polymesh-dart-account-key";
pub const DART_GEN_ASSET_KEY: &'static [u8] = b"polymesh-dart-asset-key";
pub const DART_GEN_ENC_KEY: &'static [u8] = b"polymesh-dart-pk-enc";

pub const DART_GEN_POSEIDON2: &'static [u8] = b"polymesh-dart-poseidon2";

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    pub static ref DART_GENS: DartBPGenerators = DartBPGenerators::new(DART_GEN_DOMAIN);

    pub static ref POSEIDON_PARAMS: PoseidonParameters = PoseidonParameters::new(DART_GEN_POSEIDON2).expect("Failed to create Poseidon parameters");
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
            POSEIDON_PARAMS = Some(
                PoseidonParameters::new(DART_GEN_POSEIDON2)
                    .expect("Failed to create Poseidon parameters"),
            );
        }
        POSEIDON_PARAMS.as_ref().unwrap()
    }
}

pub struct PoseidonParameters {
    pub params: Poseidon2Params<PallasScalar>,
}

impl PoseidonParameters {
    pub fn new(label: &[u8]) -> Result<Self, Error> {
        let mut rng = rand_chacha::ChaCha20Rng::from_seed(Blake2s256::digest(label).into());
        let full_rounds = 8;
        let partial_rounds = 56;
        Ok(Self {
            params: Poseidon2Params::new_with_randoms(&mut rng, 3, 5, full_rounds, partial_rounds)?,
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
        let balance_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : balance_gen"
        ]);
        let counter_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : counter_gen"
        ]);
        let asset_id_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : asset_id_gen"
        ]);
        let rho_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : rho_gen"
        ]);
        let current_rho_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : current_rho_gen"
        ]);
        let randomness_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : randomness_gen"
        ]);
        let identity_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : identity_gen"
        ]);

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
        let sig_key_gen =
            affine_group_elem_from_try_and_incr::<PallasA, Blake2b512>(&concat_slices![
                label,
                b" : sig_key_gen"
            ]);
        let enc_key_gen =
            affine_group_elem_from_try_and_incr::<PallasA, Blake2b512>(&concat_slices![
                label,
                b" : enc_key_gen"
            ]);

        let account_comm_key =
            AccountCommitmentKey::new::<Blake2b512>(DART_GEN_ACCOUNT_KEY, sig_key_gen);

        let leg_asset_value_gen =
            affine_group_elem_from_try_and_incr::<PallasA, Blake2b512>(&concat_slices![
                label,
                b" : leg_asset_value_gen"
            ]);

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

pub trait AccountStateUpdate {
    fn account_state_commitment(&self) -> AccountStateCommitment;
    fn nullifier(&self) -> AccountStateNullifier;
    fn root_block(&self) -> BlockNumber;
}

pub trait AccountLookup {
    /// Get the encryption public key for the account.
    fn get_account_enc_pk(&self, account: &AccountPublicKey) -> Option<EncryptionPublicKey>;

    /// Get the account public key for the given encryption public key.
    fn get_account(&self, enc_pk: &EncryptionPublicKey) -> Option<AccountPublicKey>;
}

#[derive(Clone, Debug, Default)]
#[cfg(feature = "std")]
pub struct AccountLookupMap {
    enc_to_acct: HashMap<EncryptionPublicKey, AccountPublicKey>,
    acct_to_enc: HashMap<AccountPublicKey, EncryptionPublicKey>,
}

#[cfg(feature = "std")]
impl AccountLookup for AccountLookupMap {
    fn get_account_enc_pk(&self, account: &AccountPublicKey) -> Option<EncryptionPublicKey> {
        self.acct_to_enc.get(account).copied()
    }

    fn get_account(&self, enc_pk: &EncryptionPublicKey) -> Option<AccountPublicKey> {
        self.enc_to_acct.get(enc_pk).copied()
    }
}

#[cfg(feature = "std")]
impl AccountLookupMap {
    pub fn new() -> Self {
        Self {
            enc_to_acct: HashMap::new(),
            acct_to_enc: HashMap::new(),
        }
    }

    pub fn ensure_unregistered(&self, keys: &AccountPublicKeys) -> Result<(), Error> {
        if self.enc_to_acct.contains_key(&keys.enc) {
            return Err(Error::AccountPublicKeyExists);
        }
        if self.acct_to_enc.contains_key(&keys.acct) {
            return Err(Error::AccountPublicKeyExists);
        }
        Ok(())
    }

    /// Register an account's encryption public key and account public key in the lookup map.
    pub fn register_account_keys(&mut self, account_pk_keys: &AccountPublicKeys) {
        self.enc_to_acct
            .insert(account_pk_keys.enc, account_pk_keys.acct);
        self.acct_to_enc
            .insert(account_pk_keys.acct, account_pk_keys.enc);
    }
}

/// The encryption public key, which can be shared freely.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    Default,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct EncryptionPublicKey(CompressedAffine);

impl EncryptionPublicKey {
    /// Creates a `EncryptionPublicKey` from a hex string.
    pub fn from_str(s: &str) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::from_str(s)?))
    }

    /// Creates a `EncryptionPublicKey` from an affine point.
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    /// Gets the affine point corresponding to the `EncryptionPublicKey`.
    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    /// Creates an `EncryptionPublicKey` from a BP encryption key.
    pub fn from_bp_key(pk: bp_keys::EncKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    /// Gets the BP encryption key corresponding to the `EncryptionPublicKey`.
    pub fn get_bp_key(&self) -> Result<bp_keys::EncKey<PallasA>, Error> {
        Ok(bp_keys::EncKey(self.get_affine()?))
    }
}

/// The encryption secret key, which should be kept private.
#[derive(
    Clone,
    Debug,
    Default,
    CanonicalSerialize,
    CanonicalDeserialize,
    PartialEq,
    Eq,
    Zeroize,
    ZeroizeOnDrop,
)]
pub struct EncryptionSecretKey(bp_keys::DecKey<PallasA>);

/// The encryption key pair, consisting of the public and secret keys.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq)]
pub struct EncryptionKeyPair {
    pub public: EncryptionPublicKey,
    pub secret: EncryptionSecretKey,
}

impl EncryptionKeyPair {
    /// Generates a new set of encryption keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let (enc, enc_pk) = bp_keys::keygen_enc(rng, dart_gens().enc_key_gen());
        Ok(Self {
            public: EncryptionPublicKey::from_bp_key(enc_pk)?,
            secret: EncryptionSecretKey(enc),
        })
    }
}

/// The account public key, which can be shared freely.
#[derive(
    Copy, Clone, MaxEncodedLen, Encode, Decode, Default, TypeInfo, Debug, PartialEq, Eq, Hash,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct AccountPublicKey(CompressedAffine);

impl AccountPublicKey {
    /// Creates a `AccountPublicKey` from a hex string.
    pub fn from_str(s: &str) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::from_str(s)?))
    }

    /// Creates a `AccountPublicKey` from an affine point.
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    /// Gets the affine point corresponding to the `AccountPublicKey`.
    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    /// Creates an `AccountPublicKey` from a BP verification key.
    pub fn from_bp_key(pk: bp_keys::VerKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    /// Gets the BP verification key corresponding to the `AccountPublicKey`.
    pub fn get_bp_key(&self) -> Result<bp_keys::VerKey<PallasA>, Error> {
        Ok(bp_keys::VerKey(self.get_affine()?))
    }
}

/// The account secret key, which should be kept private.
#[derive(
    Clone,
    Debug,
    Default,
    CanonicalSerialize,
    CanonicalDeserialize,
    PartialEq,
    Eq,
    Zeroize,
    ZeroizeOnDrop,
)]
pub struct AccountSecretKey(bp_keys::SigKey<PallasA>);

/// The account key pair, consisting of the public and secret keys.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq)]
pub struct AccountKeyPair {
    pub public: AccountPublicKey,
    pub secret: AccountSecretKey,
}

impl AccountKeyPair {
    /// Generates a new set of account keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let (account, account_pk) = bp_keys::keygen_sig(rng, dart_gens().sig_key_gen());
        Ok(Self {
            public: AccountPublicKey::from_bp_key(account_pk)?,
            secret: AccountSecretKey(account),
        })
    }

    /// Initializes a new asset state for the account.
    pub fn init_asset_state<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<AccountAssetState, Error> {
        AccountAssetState::new(rng, &self, asset_id, counter, identity)
    }

    pub fn account_state<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<AccountState, Error> {
        let params = poseidon_params();
        let id = hash_identity::<PallasScalar>(identity);
        let state = BPAccountState::new(
            rng,
            id,
            self.secret.0.0,
            asset_id,
            counter,
            params.params.clone(),
        )?;
        Ok(state.try_into()?)
    }
}

/// The pair of public keys for an account: the encryption public key and the account public key.
#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
pub struct AccountPublicKeys {
    pub enc: EncryptionPublicKey,
    pub acct: AccountPublicKey,
}

/// The pair of key pairs for an account: the encryption key pair and the account key pair.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq)]
pub struct AccountKeys {
    pub enc: EncryptionKeyPair,
    pub acct: AccountKeyPair,
}

impl AccountKeys {
    /// Generates a new set of account keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let enc = EncryptionKeyPair::rand(rng)?;
        let acct = AccountKeyPair::rand(rng)?;
        Ok(Self { enc, acct })
    }

    /// Genreates a new set of account keys using the provided string as a seed.
    pub fn from_seed(seed: &str) -> Result<Self, Error> {
        let mut rng =
            rand_chacha::ChaCha20Rng::from_seed(Blake2s256::digest(seed.as_bytes()).into());
        Self::rand(&mut rng)
    }

    /// Initializes a new asset state for the account.
    pub fn init_asset_state<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<AccountAssetState, Error> {
        self.acct.init_asset_state(rng, asset_id, counter, identity)
    }

    /// Returns the public keys for the account.
    pub fn public_keys(&self) -> AccountPublicKeys {
        AccountPublicKeys {
            enc: self.enc.public,
            acct: self.acct.public,
        }
    }
}

#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "sqlx", derive(sqlx::FromRow))]
pub struct AccountState {
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub identity: WrappedCanonical<PallasScalar>,
    pub asset_id: AssetId,
    pub rho: WrappedCanonical<PallasScalar>,
    pub current_rho: WrappedCanonical<PallasScalar>,
    pub randomness: WrappedCanonical<PallasScalar>,
}

impl AccountState {
    pub fn bp_state(
        &self,
        account: &AccountKeyPair,
    ) -> Result<(BPAccountState, BPAccountStateCommitment), Error> {
        let state = BPAccountState {
            sk: account.secret.0.0,
            id: self.identity.decode()?,
            balance: self.balance,
            counter: self.counter,
            asset_id: self.asset_id,
            rho: self.rho.decode()?,
            current_rho: self.current_rho.decode()?,
            randomness: self.randomness.decode()?,
        };
        let commitment = state.commit(dart_gens().account_comm_key())?;
        Ok((state, commitment))
    }

    pub fn commitment(&self, account: &AccountKeyPair) -> Result<AccountStateCommitment, Error> {
        let (_state, commitment) = self.bp_state(account)?;
        AccountStateCommitment::from_affine(commitment.0)
    }

    pub fn nullifier(&self) -> Result<AccountStateNullifier, Error> {
        let account_comm_key = dart_gens().account_comm_key();
        let current_rho = self.current_rho.decode()?;
        let nullifier = (account_comm_key.current_rho_gen() * current_rho).into();
        AccountStateNullifier::from_affine(nullifier)
    }
}

impl TryFrom<BPAccountState> for AccountState {
    type Error = Error;

    fn try_from(state: BPAccountState) -> Result<Self, Self::Error> {
        Ok(Self {
            balance: state.balance,
            counter: state.counter,
            asset_id: state.asset_id,
            identity: WrappedCanonical::wrap(&state.id)?,
            rho: WrappedCanonical::wrap(&state.rho)?,
            current_rho: WrappedCanonical::wrap(&state.current_rho)?,
            randomness: WrappedCanonical::wrap(&state.randomness)?,
        })
    }
}

#[derive(Copy, Clone, MaxEncodedLen, Encode, Decode, TypeInfo, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccountStateNullifier(CompressedAffine);

impl AccountStateNullifier {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }
}

#[derive(Copy, Clone, MaxEncodedLen, Encode, Decode, TypeInfo, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccountStateCommitment(CompressedAffine);

impl AccountStateCommitment {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    pub fn as_leaf_value(&self) -> Result<CompressedLeafValue<AccountTreeConfig>, Error> {
        Ok(self.0.into())
    }

    pub fn as_commitment(&self) -> Result<BPAccountStateCommitment, Error> {
        Ok(bp_account::AccountStateCommitment(self.get_affine()?))
    }
}

impl From<CompressedLeafValue<AccountTreeConfig>> for AccountStateCommitment {
    fn from(ca: CompressedLeafValue<AccountTreeConfig>) -> Self {
        Self(ca.into())
    }
}

impl From<CompressedAffine> for AccountStateCommitment {
    fn from(ca: CompressedAffine) -> Self {
        Self(ca)
    }
}

impl From<AccountStateCommitment> for CompressedAffine {
    fn from(asc: AccountStateCommitment) -> Self {
        asc.0
    }
}

#[derive(Clone, Debug)]
pub struct AccountAssetStateChange {
    pub current_state: BPAccountState,
    pub current_commitment: BPAccountStateCommitment,
    pub new_state: BPAccountState,
    pub new_commitment: BPAccountStateCommitment,
}

impl AccountAssetStateChange {
    pub fn commitment(&self) -> Result<AccountStateCommitment, Error> {
        AccountStateCommitment::from_affine(self.new_commitment.0)
    }

    pub fn get_path<
        C: CurveTreeConfig<
                F0 = <PallasParameters as CurveConfig>::ScalarField,
                F1 = <VestaParameters as CurveConfig>::ScalarField,
                P0 = PallasParameters,
                P1 = VestaParameters,
            >,
    >(
        &self,
        tree_lookup: &impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<CurveTreePath<ACCOUNT_TREE_L, C>, Error> {
        tree_lookup.get_path_to_leaf(CompressedLeafValue::from_affine(self.current_commitment.0)?)
    }
}

#[derive(Clone, Debug, Encode, Decode)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccountAssetState {
    pub current_state: AccountState,
    pub pending_state: Option<AccountState>,
}

impl AccountAssetState {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<Self, Error> {
        let current_state = account.account_state(rng, asset_id, counter, identity)?;
        Ok(Self {
            current_state,
            pending_state: None,
        })
    }

    pub fn current_commitment(
        &self,
        account: &AccountKeyPair,
    ) -> Result<AccountStateCommitment, Error> {
        self.current_state.commitment(account)
    }

    pub fn asset_id(&self) -> AssetId {
        self.current_state.asset_id
    }

    pub fn bp_current_state(
        &self,
        account: &AccountKeyPair,
    ) -> Result<(BPAccountState, BPAccountStateCommitment), Error> {
        self.current_state.bp_state(account)
    }

    fn state_change(
        &mut self,
        account: &AccountKeyPair,
        update: impl FnOnce(&BPAccountState) -> Result<BPAccountState, Error>,
    ) -> Result<AccountAssetStateChange, Error> {
        let (current_state, current_commitment) = self.bp_current_state(account)?;

        // Update the state.
        let new_state = update(&current_state)?;
        let new_commitment = new_state.commit(dart_gens().account_comm_key())?;

        // Set the pending state.
        self.pending_state = Some(new_state.clone().try_into()?);

        Ok(AccountAssetStateChange {
            current_state,
            current_commitment,
            new_state,
            new_commitment,
        })
    }

    pub fn mint(
        &mut self,
        account: &AccountKeyPair,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(account, |state| Ok(state.get_state_for_mint(amount)?))
    }

    pub fn get_sender_affirm_state(
        &mut self,
        account: &AccountKeyPair,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(account, |state| Ok(state.get_state_for_send(amount)?))
    }

    pub fn get_receiver_affirm_state(
        &mut self,
        account: &AccountKeyPair,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(account, |state| Ok(state.get_state_for_receive()))
    }

    pub fn get_state_for_claiming_received(
        &mut self,
        account: &AccountKeyPair,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(account, |state| {
            Ok(state.get_state_for_claiming_received(amount)?)
        })
    }

    pub fn get_state_for_reversing_send(
        &mut self,
        account: &AccountKeyPair,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(account, |state| {
            Ok(state.get_state_for_reversing_send(amount)?)
        })
    }

    pub fn get_state_for_decreasing_counter(
        &mut self,
        account: &AccountKeyPair,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(account, |state| {
            Ok(state.get_state_for_decreasing_counter(None)?)
        })
    }

    pub fn commit_pending_state(&mut self) -> Result<bool, Error> {
        match self.pending_state.take() {
            Some(pending_state) => {
                self.current_state = pending_state;
                Ok(true)
            }
            None => Ok(false),
        }
    }
}

/// Represents the state of an asset in the Dart BP protocol.
#[derive(Clone, Debug, Encode, Decode, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AssetState<T: DartLimits = ()> {
    pub asset_id: AssetId,
    pub mediators: BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetMediators>,
    pub auditors: BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
}

impl<T: DartLimits> AssetState<T> {
    /// Creates a new asset state with the given asset ID, mediator status, and public key.
    pub fn new(
        asset_id: AssetId,
        mediators: &[EncryptionPublicKey],
        auditors: &[EncryptionPublicKey],
    ) -> Self {
        let mut state = Self {
            asset_id,
            auditors: Default::default(),
            mediators: Default::default(),
        };

        for mediator in mediators {
            state
                .mediators
                .try_insert(*mediator)
                .expect("Too many asset mediators");
        }
        for auditor in auditors {
            state
                .auditors
                .try_insert(*auditor)
                .expect("Too many asset auditors");
        }

        state
    }

    /// Creates a new asset state with the given asset ID, mediator status, and public key.
    pub fn new_bounded(
        asset_id: AssetId,
        mediators: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetMediators>,
        auditors: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
    ) -> Self {
        Self {
            asset_id,
            auditors: auditors.clone(),
            mediators: mediators.clone(),
        }
    }

    pub fn keys(&self) -> Vec<(bool, PallasA)> {
        let mut keys = Vec::with_capacity(self.auditors.len() + self.mediators.len());
        for mediator in &self.mediators {
            keys.push((false, mediator.get_affine().unwrap()));
        }
        for auditor in &self.auditors {
            keys.push((true, auditor.get_affine().unwrap()));
        }
        keys
    }

    pub fn asset_data(&self) -> Result<AssetCommitmentData, Error> {
        let tree_params = get_asset_curve_tree_parameters();
        let asset_comm_params = get_asset_commitment_parameters();
        let asset_data = AssetCommitmentData::new(
            self.asset_id,
            self.keys(),
            asset_comm_params,
            tree_params.odd_parameters.delta,
        )?;
        Ok(asset_data)
    }

    pub fn commitment(&self) -> Result<CompressedLeafValue<AssetTreeConfig>, Error> {
        let asset_data = self.asset_data()?;
        CompressedLeafValue::from_affine(asset_data.commitment)
    }
}

/// Represents a tree of asset states in the Dart BP protocol.
#[cfg(feature = "std")]
pub struct AssetCurveTree {
    pub tree: FullCurveTree<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>,
    assets: HashMap<AssetId, (LeafIndex, AssetState)>,
}

#[cfg(feature = "std")]
impl AssetCurveTree {
    /// Creates a new instance of `AssetCurveTree` with the specified parameters.
    pub fn new() -> Result<Self, Error> {
        Ok(Self {
            tree: FullCurveTree::new_with_capacity(ASSET_TREE_HEIGHT, ASSET_TREE_GENS)?,
            assets: HashMap::new(),
        })
    }

    /// Returns the asset state for the given asset ID, if it exists.
    pub fn get_asset_state(&self, asset_id: AssetId) -> Option<AssetState> {
        self.assets.get(&asset_id).map(|(_, state)| state.clone())
    }

    /// Sets the asset state in the tree and returns the index of the asset state.
    pub fn set_asset_state(&mut self, state: AssetState) -> Result<LeafIndex, Error> {
        let asset_id = state.asset_id;
        // Get the new asset state commitment.
        let asset_data = state.asset_data()?;
        let leaf = CompressedLeafValue::from_affine(asset_data.commitment)?;

        // Update or insert the asset state.
        use std::collections::hash_map::Entry;
        match self.assets.entry(asset_id) {
            Entry::Occupied(mut entry) => {
                let (index, existing_state) = entry.get_mut();
                *existing_state = state;
                let index = *index;
                // Update the leaf in the curve tree.
                self.tree.update(leaf, index)?;

                Ok(index)
            }
            Entry::Vacant(entry) => {
                let index = self.tree.insert(leaf)?;
                entry.insert((index, state));

                Ok(index)
            }
        }
    }

    pub fn get_asset_state_path(
        &self,
        asset_id: AssetId,
    ) -> Option<CurveTreePath<ASSET_TREE_L, AssetTreeConfig>> {
        let (leaf_index, _) = self.assets.get(&asset_id)?;
        self.tree.get_path_to_leaf_index(*leaf_index).ok()
    }

    pub fn params(&self) -> &CurveTreeParameters<AssetTreeConfig> {
        self.tree.params()
    }

    pub fn root_node(
        &self,
    ) -> Result<CompressedCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>, Error> {
        self.tree.root_node()
    }

    pub fn set_block_number(&mut self, block_number: BlockNumber) -> Result<(), Error> {
        self.tree.set_block_number(block_number)?;
        Ok(())
    }

    pub fn store_root(&mut self) -> Result<(), Error> {
        self.tree.store_root()?;
        Ok(())
    }
}

#[cfg(feature = "std")]
impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig> for &AssetCurveTree {
    fn get_block_root(
        &self,
        block_number: BlockNumber,
    ) -> Option<CompressedCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>> {
        self.tree.fetch_root(block_number).ok()
    }

    fn params(&self) -> &CurveTreeParameters<AssetTreeConfig> {
        self.tree.params()
    }
}

/// Account asset registration proof.  Report section 5.1.3 "Account Registration".
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct AccountAssetRegistrationProof {
    pub account: AccountPublicKey,
    pub asset_id: AssetId,
    pub counter: NullifierSkGenCounter,
    pub account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<account_registration::RegTxnProof<PallasA>>,
}

impl AccountAssetRegistrationProof {
    /// Generate a new account state for an asset and a registration proof for it.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
    ) -> Result<(Self, AccountAssetState), Error> {
        let pk = account.public;
        let account_state = account.init_asset_state(rng, asset_id, counter, identity)?;
        let (bp_state, commitment) = account_state.bp_current_state(account)?;
        let params = poseidon_params();
        let gens = dart_gens();
        let (proof, nullifier) = account_registration::RegTxnProof::new(
            rng,
            pk.get_affine()?,
            &bp_state,
            commitment,
            counter,
            identity,
            gens.account_comm_key(),
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            &params.params,
            None,
        )?;
        Ok((
            Self {
                account: pk,
                asset_id,
                counter,
                account_state_commitment: AccountStateCommitment::from_affine(commitment.0)?,
                nullifier: AccountStateNullifier::from_affine(nullifier)?,

                proof: WrappedCanonical::wrap(&proof)?,
            },
            account_state,
        ))
    }

    /// Verifies the account asset registration proof against the provided public key, asset ID, and account state commitment.
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let proof = self.proof.decode()?;
        let params = poseidon_params();
        let id = hash_identity::<PallasScalar>(identity);
        proof.verify(
            rng,
            id,
            &self.account.get_affine()?,
            self.asset_id,
            &self.account_state_commitment.as_commitment()?,
            self.counter,
            self.nullifier.get_affine()?,
            identity,
            dart_gens().account_comm_key(),
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            &params.params,
            None,
        )?;
        Ok(())
    }
}

fn try_block_number<T: TryInto<BlockNumber>>(block_number: T) -> Result<BlockNumber, Error> {
    block_number
        .try_into()
        .map_err(|_| Error::CurveTreeBlockNumberNotFound)
}

/// Asset minting proof.  Report section 5.1.4 "Increase Asset Supply".
#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct AssetMintingProof<C: CurveTreeConfig = AccountTreeConfig> {
    // Public inputs.
    pub pk: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    // proof
    proof: WrappedCanonical<bp_account::MintTxnProof<ACCOUNT_TREE_L, C::F0, C::F1, C::P0, C::P1>>,
}

impl<C: CurveTreeConfig> core::fmt::Debug for AssetMintingProof<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("AssetMintingProof")
            .field("pk", &self.pk)
            .field("asset_id", &self.asset_id)
            .field("amount", &self.amount)
            .field("root_block", &self.root_block)
            .field(
                "updated_account_state_commitment",
                &self.updated_account_state_commitment,
            )
            .field("nullifier", &self.nullifier)
            .finish()
    }
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> AssetMintingProof<C>
{
    /// Generate a new asset minting proof.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        amount: Balance,
    ) -> Result<Self, Error> {
        // Generate a new minting state for the account asset.
        let state_change = account_asset.mint(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;
        let pk = account.public;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root_node()?;
        let root = root.root_node()?;

        let (proof, nullifier) = bp_account::MintTxnProof::new(
            rng,
            pk.get_affine()?,
            amount,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            b"",
            tree_lookup.params(),
            dart_gens().account_comm_key(),
        )?;
        Ok(Self {
            pk,
            asset_id: account_asset.asset_id(),
            amount,
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for asset minting proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        let proof = self.proof.decode()?;
        proof.verify(
            self.pk.get_affine()?,
            self.asset_id,
            self.amount,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            &root,
            b"",
            tree_roots.params(),
            dart_gens().account_comm_key(),
            rng,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for AssetMintingProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SettlementHash(#[cfg_attr(feature = "serde", serde(with = "human_hex"))] pub [u8; 32]);

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub enum SettlementRef {
    /// ID based reference.
    #[cfg_attr(feature = "utoipa", schema(example = json!({"ID": 1})))]
    ID(#[codec(compact)] SettlementId),
    /// Hash based reference.
    #[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
    Hash(SettlementHash),
}

impl From<SettlementId> for SettlementRef {
    fn from(id: SettlementId) -> Self {
        SettlementRef::ID(id)
    }
}

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct LegRef {
    /// The settlement reference.
    pub settlement: SettlementRef,
    /// The leg ID within the settlement.
    #[cfg_attr(feature = "utoipa", schema(example = 0, value_type = u8))]
    pub leg_id: LegId,
}

impl LegRef {
    pub fn new(settlement: SettlementRef, leg_id: LegId) -> Self {
        Self { settlement, leg_id }
    }

    /// Returns the leg ID.
    pub fn leg_id(&self) -> LegId {
        self.leg_id
    }

    /// Returns the settlement ID if the settlement reference is an ID.
    pub fn settlement_id(&self) -> Option<SettlementId> {
        if let SettlementRef::ID(id) = &self.settlement {
            Some(*id)
        } else {
            None
        }
    }

    /// The settlement/leg context to tie proofs to a leg.
    pub fn context(&self) -> String {
        format!("{:?}-{}", self.settlement, self.leg_id)
    }
}

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub enum LegRole {
    Sender,
    Receiver,
    Auditor(u8),
    Mediator(u8),
}

impl LegRole {
    pub fn is_sender_or_receiver(&self) -> bool {
        matches!(self, LegRole::Sender | LegRole::Receiver)
    }

    pub fn is_sender(&self) -> bool {
        matches!(self, LegRole::Sender)
    }
}

/// The decrypted leg details in the Dart BP protocol.
#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct Leg {
    pub sender: AccountPublicKey,
    pub receiver: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
}

impl Leg {
    pub fn new(
        sender: AccountPublicKey,
        receiver: AccountPublicKey,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<Self, Error> {
        Ok(Self {
            sender,
            receiver,
            asset_id,
            amount,
        })
    }

    pub fn encrypt<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        sender: EncryptionPublicKey,
        receiver: EncryptionPublicKey,
        asset_keys: &[(bool, PallasA)],
    ) -> Result<(bp_leg::Leg<PallasA>, LegEncrypted, LegEncryptionRandomness), Error> {
        let leg = bp_leg::Leg::new(
            self.sender.get_affine()?,
            self.receiver.get_affine()?,
            asset_keys.into(),
            self.amount,
            self.asset_id,
        )?;
        let (leg_enc, leg_enc_rand) = leg.encrypt::<_, Blake2b512>(
            rng,
            sender.get_affine()?,
            receiver.get_affine()?,
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok((
            leg,
            LegEncrypted::new(leg_enc)?,
            LegEncryptionRandomness::new(leg_enc_rand)?,
        ))
    }

    pub fn sender(&self) -> Result<AccountPublicKey, Error> {
        Ok(self.sender)
    }

    pub fn receiver(&self) -> Result<AccountPublicKey, Error> {
        Ok(self.receiver)
    }

    pub fn asset_id(&self) -> AssetId {
        self.asset_id
    }

    pub fn amount(&self) -> Balance {
        self.amount
    }
}

/// A helper type to build the encrypted leg and its proof in the Dart BP protocol.
#[derive(Clone, Debug, Encode, Decode)]
pub struct LegBuilder {
    pub sender: AccountPublicKeys,
    pub receiver: AccountPublicKeys,
    pub asset: AssetState,
    pub amount: Balance,
}

impl LegBuilder {
    /// Creates a new leg with the given sender, receiver, asset ID, amount, and optional mediator.
    pub fn new(
        sender: AccountPublicKeys,
        receiver: AccountPublicKeys,
        asset: AssetState,
        amount: Balance,
    ) -> Self {
        Self {
            sender,
            receiver,
            asset,
            amount,
        }
    }

    pub fn encrypt_and_prove<
        R: RngCore + CryptoRng,
        C: CurveTreeConfig<
                F0 = <VestaParameters as CurveConfig>::ScalarField,
                F1 = <PallasParameters as CurveConfig>::ScalarField,
                P0 = VestaParameters,
                P1 = PallasParameters,
            >,
    >(
        self,
        rng: &mut R,
        ctx: &[u8],
        asset_tree: &impl CurveTreeLookup<ASSET_TREE_L, ASSET_TREE_M, C>,
    ) -> Result<SettlementLegProof<C>, Error> {
        let asset_data = self.asset.asset_data()?;

        let leg = Leg::new(
            self.sender.acct,
            self.receiver.acct,
            self.asset.asset_id,
            self.amount,
        )?;
        let (leg, leg_enc, leg_enc_rand) =
            leg.encrypt(rng, self.sender.enc, self.receiver.enc, &asset_data.keys)?;

        let leg_proof = SettlementLegProof::new(
            rng,
            leg,
            leg_enc,
            &leg_enc_rand,
            asset_data,
            ctx,
            asset_tree,
        )?;

        Ok(leg_proof)
    }
}

#[derive(Clone, Debug, Encode, Decode)]
pub struct SettlementBuilder<T: DartLimits = ()> {
    pub memo: Vec<u8>,
    pub legs: Vec<LegBuilder>,
    _marker: PhantomData<T>,
}

impl<T: DartLimits> SettlementBuilder<T> {
    pub fn new(memo: &[u8]) -> Self {
        Self {
            memo: memo.to_vec(),
            legs: Vec::new(),
            _marker: PhantomData,
        }
    }

    pub fn leg(mut self, leg: LegBuilder) -> Self {
        self.legs.push(leg);
        self
    }

    pub fn encrypt_and_prove<
        R: RngCore + CryptoRng,
        C: CurveTreeConfig<
                F0 = <VestaParameters as CurveConfig>::ScalarField,
                F1 = <PallasParameters as CurveConfig>::ScalarField,
                P0 = VestaParameters,
                P1 = PallasParameters,
            >,
    >(
        self,
        rng: &mut R,
        asset_tree: impl CurveTreeLookup<ASSET_TREE_L, ASSET_TREE_M, C>,
    ) -> Result<SettlementProof<T, C>, Error> {
        let memo = BoundedVec::try_from(self.memo)
            .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        let root_block = asset_tree.get_block_number()?;

        let mut legs = Vec::with_capacity(self.legs.len());

        for (idx, leg_builder) in self.legs.into_iter().enumerate() {
            let ctx = (&memo, idx as u8).encode();
            let leg_proof = leg_builder.encrypt_and_prove(rng, &ctx, &asset_tree)?;
            legs.push(leg_proof);
        }

        let legs =
            BoundedVec::try_from(legs).map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        Ok(SettlementProof {
            memo,
            root_block: try_block_number(root_block)?,
            legs,
        })
    }
}

#[derive(Clone, Debug, Encode, Decode, TypeInfo)]
#[scale_info(skip_type_params(T, C))]
pub struct SettlementProof<T: DartLimits = (), C: CurveTreeConfig = AssetTreeConfig> {
    pub memo: BoundedVec<u8, T::MaxSettlementMemoLength>,
    pub root_block: BlockNumber,

    pub legs: BoundedVec<SettlementLegProof<C>, T::MaxSettlementLegs>,
}

impl<T: DartLimits, C: CurveTreeConfig> PartialEq for SettlementProof<T, C> {
    fn eq(&self, other: &Self) -> bool {
        self.memo == other.memo && self.root_block == other.root_block && self.legs == other.legs
    }
}

impl<T: DartLimits, C: CurveTreeConfig> Eq for SettlementProof<T, C> {}

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <VestaParameters as CurveConfig>::ScalarField,
            F1 = <PallasParameters as CurveConfig>::ScalarField,
            P0 = VestaParameters,
            P1 = PallasParameters,
        >,
> SettlementProof<T, C>
{
    pub fn hash(&self) -> SettlementHash {
        let mut hasher = Blake2s256::new();
        let data = self.encode();
        hasher.update(&data);
        SettlementHash(hasher.finalize().into())
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        asset_tree: impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = asset_tree
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for settlement proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        let params = asset_tree.params();
        for (idx, leg) in self.legs.iter().enumerate() {
            let ctx = (&self.memo, idx as u8).encode();
            leg.verify(&ctx, &root, params, rng)?;
        }
        Ok(())
    }
}

/// The proof for a settlement leg in the Dart BP protocol.
///
/// This is to prove that the leg includes the correct encryption of the leg details and
/// that the correct auditor/mediator for the asset is included in the leg.
#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SettlementLegProof<C: CurveTreeConfig = AssetTreeConfig> {
    pub leg_enc: LegEncrypted,

    proof: WrappedCanonical<bp_leg::SettlementTxnProof<ASSET_TREE_L, C::F1, C::F0, C::P1, C::P0>>,
}

impl<C: CurveTreeConfig> core::fmt::Debug for SettlementLegProof<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SettlementLegProof")
            .field("leg_enc", &self.leg_enc)
            .field("proof", &self.proof)
            .finish()
    }
}

impl<
    C: CurveTreeConfig<
            F0 = <VestaParameters as CurveConfig>::ScalarField,
            F1 = <PallasParameters as CurveConfig>::ScalarField,
            P0 = VestaParameters,
            P1 = PallasParameters,
        >,
> SettlementLegProof<C>
{
    pub(crate) fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg: bp_leg::Leg<PallasA>,
        leg_enc: LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        asset_data: AssetCommitmentData,
        ctx: &[u8],
        asset_tree: &impl CurveTreeLookup<ASSET_TREE_L, ASSET_TREE_M, C>,
    ) -> Result<Self, Error> {
        let asset_path = asset_tree.get_path_to_leaf_index(leg.asset_id as LeafIndex)?;
        let asset_comm_params = get_asset_commitment_parameters();

        let proof = bp_leg::SettlementTxnProof::new(
            rng,
            leg,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            asset_path,
            asset_data,
            ctx,
            asset_tree.params(),
            asset_comm_params,
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_enc,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn mediator_count(&self) -> Result<usize, Error> {
        self.get_mediator_ids().map(|ids| ids.len())
    }

    pub fn get_mediator_ids(&self) -> Result<Vec<MediatorId>, Error> {
        let leg_enc = self.leg_enc.decode()?;
        let mediators = leg_enc
            .eph_pk_auds_meds
            .iter()
            .enumerate()
            .filter(|(_idx, (is_auditor, _pk))| !is_auditor)
            .map(|(idx, _)| idx as MediatorId)
            .collect();
        Ok(mediators)
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        ctx: &[u8],
        root: &Root<ASSET_TREE_L, ASSET_TREE_M, C::P0, C::P1>,
        params: &CurveTreeParameters<C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let asset_comm_params = get_asset_commitment_parameters();
        let leg_enc = self.leg_enc.decode()?;
        log::debug!("Verify leg: {:?}", leg_enc);
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.clone(),
            &root,
            ctx,
            params,
            asset_comm_params,
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok(())
    }
}

/// Represents a hashed settlement proof in the Dart BP protocol.
///
/// This allows building the settlement off-chain and collecting the leg affirmations
/// before submitting the settlement to the chain.
#[derive(Clone, Debug, Encode, Decode, TypeInfo)]
#[scale_info(skip_type_params(T, C))]
pub struct HashedSettlementProof<T: DartLimits = (), C: CurveTreeConfig = AssetTreeConfig> {
    /// The settlement proof containing the memo, root, and legs.
    pub settlement: SettlementProof<T, C>,
    /// The hash of the settlement, used to tie the leg affirmations to this settlement.
    pub hash: SettlementHash,
}

impl<T: DartLimits, C: CurveTreeConfig> PartialEq for HashedSettlementProof<T, C> {
    fn eq(&self, other: &Self) -> bool {
        self.settlement == other.settlement && self.hash == other.hash
    }
}

impl<T: DartLimits, C: CurveTreeConfig> Eq for HashedSettlementProof<T, C> {}

/// Counts of the legs and sender/receiver affirmations in a batched settlement.
#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct BatchedSettlementCounts {
    pub leg_count: u32,
    pub sender_count: u64,
    pub receiver_count: u64,
}

/// Represents the affirmation proofs for each leg in a settlement.
/// This includes the sender, and receiver affirmation proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo)]
pub struct BatchedSettlementLegAffirmations<C: CurveTreeConfig = AccountTreeConfig> {
    /// The sender's affirmation proof.
    pub sender: Option<SenderAffirmationProof<C>>,
    /// The receiver's affirmation proof.
    pub receiver: Option<ReceiverAffirmationProof<C>>,
}

impl<C: CurveTreeConfig> PartialEq for BatchedSettlementLegAffirmations<C> {
    fn eq(&self, other: &Self) -> bool {
        self.sender == other.sender && self.receiver == other.receiver
    }
}

/// A batched settlement proof allows including the sender and receiver affirmation proofs
/// with the settlement creation proof to reduce the number of transactions
/// required to finalize a settlement.
#[derive(Clone, Debug, Encode, Decode, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct BatchedSettlementProof<
    T: DartLimits = (),
    C: CurveTreeConfig = AssetTreeConfig,
    A: CurveTreeConfig = AccountTreeConfig,
> {
    /// The settlement proof containing the memo, root, and legs.
    pub hashed_settlement: HashedSettlementProof<T, C>,

    /// The leg affirmations for each leg in the settlement.
    pub leg_affirmations: BoundedVec<BatchedSettlementLegAffirmations<A>, T::MaxSettlementLegs>,
}

impl<T: DartLimits, C: CurveTreeConfig, A: CurveTreeConfig> PartialEq
    for BatchedSettlementProof<T, C, A>
{
    fn eq(&self, other: &Self) -> bool {
        self.hashed_settlement == other.hashed_settlement
            && self.leg_affirmations == other.leg_affirmations
    }
}

impl<T: DartLimits, C: CurveTreeConfig, A: CurveTreeConfig> Eq for BatchedSettlementProof<T, C, A> {}

impl<T: DartLimits, C: CurveTreeConfig, A: CurveTreeConfig> BatchedSettlementProof<T, C, A> {
    /// The settlemetn reference using the hash of the settlement.
    pub fn settlement_ref(&self) -> SettlementRef {
        SettlementRef::Hash(self.hashed_settlement.hash)
    }

    /// The settlement creation proof.
    pub fn settlement_proof(&self) -> &SettlementProof<T, C> {
        &self.hashed_settlement.settlement
    }

    /// Get leg and sender/receiver affirmation counts.
    pub fn count_leg_affirmations(&self) -> BatchedSettlementCounts {
        let mut leg_count = 0;
        let mut sender_count = 0;
        let mut receiver_count = 0;

        for leg_aff in &self.leg_affirmations {
            leg_count += 1;
            if leg_aff.sender.is_some() {
                sender_count += 1;
            }
            if leg_aff.receiver.is_some() {
                receiver_count += 1;
            }
        }

        BatchedSettlementCounts {
            leg_count,
            sender_count,
            receiver_count,
        }
    }

    /// Check leg references in affirmation proofs.
    ///
    /// Returns `true` if all leg references match the settlement legs.
    pub fn check_leg_references(&self) -> bool {
        let settlement = self.settlement_ref();
        for (idx, leg_aff) in self.leg_affirmations.iter().enumerate() {
            let leg_ref = LegRef::new(settlement, idx as LegId);
            if let Some(sender) = &leg_aff.sender {
                if sender.leg_ref != leg_ref {
                    return false;
                }
            }
            if let Some(receiver) = &leg_aff.receiver {
                if receiver.leg_ref != leg_ref {
                    return false;
                }
            }
        }
        true
    }
}

pub type WrappedLegEncryptionRandomness =
    WrappedCanonical<bp_leg::LegEncryptionRandomness<PallasScalar>>;

#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
pub struct LegEncryptionRandomness(WrappedLegEncryptionRandomness);

impl LegEncryptionRandomness {
    pub fn new(rand: bp_leg::LegEncryptionRandomness<PallasScalar>) -> Result<Self, Error> {
        Ok(Self(WrappedCanonical::wrap(&rand)?))
    }

    pub fn decode(&self) -> Result<bp_leg::LegEncryptionRandomness<PallasScalar>, Error> {
        self.0.decode()
    }
}

pub type WrappedLegEncryption = WrappedCanonical<bp_leg::LegEncryption<PallasA>>;

/// Represents an encrypted leg in the Dart BP protocol.  Stored onchain.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
pub struct LegEncrypted(WrappedLegEncryption);

impl LegEncrypted {
    pub fn new(leg_enc: bp_leg::LegEncryption<PallasA>) -> Result<Self, Error> {
        Ok(Self(WrappedCanonical::wrap(&leg_enc)?))
    }

    pub fn decode(&self) -> Result<bp_leg::LegEncryption<PallasA>, Error> {
        self.0.decode()
    }

    /// Attempt to decrypt the leg using the provided key pair and optional auditor/mediator key index.
    pub fn try_decrypt_with_key(
        &self,
        keys: &EncryptionKeyPair,
        key_index: Option<usize>,
        max_asset_id: Option<AssetId>,
    ) -> Result<(Leg, usize), Error> {
        let enc_gen = dart_gens().leg_asset_value_gen();
        let leg_enc = self.decode()?;
        let (key_index, (sender, receiver, asset_id, amount)) = if let Some(key_index) = key_index {
            // The key index is provided, use it directly.
            (
                key_index,
                leg_enc.decrypt_given_key_with_limits(
                    &keys.secret.0.0,
                    key_index,
                    enc_gen,
                    max_asset_id,
                    None,
                )?,
            )
        } else {
            // No key index provided, try all key indices until one works.
            let max_keys = leg_enc.eph_pk_auds_meds.len();
            let mut idx = 0;
            loop {
                if let Ok(res) = leg_enc.decrypt_given_key_with_limits(
                    &keys.secret.0.0,
                    idx,
                    enc_gen,
                    max_asset_id,
                    None,
                ) {
                    break (idx, res);
                }
                idx += 1;
                if idx >= max_keys {
                    return Err(Error::LegDecryptionError(
                        "Failed to decrypt leg with provided key".to_string(),
                    ));
                }
            }
        };
        Ok((
            Leg {
                sender: AccountPublicKey::from_affine(sender)?,
                receiver: AccountPublicKey::from_affine(receiver)?,
                asset_id,
                amount,
            },
            key_index,
        ))
    }

    pub fn get_encryption_randomness(
        &self,
        role: LegRole,
        keys: &EncryptionKeyPair,
    ) -> Result<LegEncryptionRandomness, Error> {
        let (rand, _leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, keys)?;
        LegEncryptionRandomness::new(rand)
    }

    fn bp_decrypt_randomness_and_leg(
        &self,
        role: LegRole,
        keys: &EncryptionKeyPair,
    ) -> Result<
        (
            bp_leg::LegEncryptionRandomness<PallasScalar>,
            bp_leg::LegEncryption<PallasA>,
            bool,
        ),
        Error,
    > {
        let is_sender = match role {
            LegRole::Sender => true,
            LegRole::Receiver => false,
            _ => {
                return Err(Error::LegDecryptionError(format!(
                    "Invalid role for encryption randomness: {:?}",
                    role
                )));
            }
        };
        let leg_enc = self.decode()?;
        let randomness =
            leg_enc.get_encryption_randomness::<Blake2b512>(&keys.secret.0.0, is_sender)?;
        Ok((randomness, leg_enc, is_sender))
    }

    pub fn decrypt(&self, role: LegRole, keys: &AccountKeys) -> Result<Leg, Error> {
        let enc_key_gen = dart_gens().enc_key_gen();
        let enc_gen = dart_gens().leg_asset_value_gen();
        let (sender, receiver, asset_id, amount) = match role {
            LegRole::Sender => {
                let (rand, leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, &keys.enc)?;
                leg_enc.decrypt_given_r_checked(
                    rand,
                    enc_key_gen,
                    enc_gen,
                    keys.acct.public.get_affine()?,
                    true,
                )?
            }
            LegRole::Receiver => {
                let (rand, leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, &keys.enc)?;
                leg_enc.decrypt_given_r_checked(
                    rand,
                    enc_key_gen,
                    enc_gen,
                    keys.acct.public.get_affine()?,
                    false,
                )?
            }
            LegRole::Auditor(idx) | LegRole::Mediator(idx) => {
                let leg_enc = self.decode()?;
                leg_enc.decrypt_given_key(&keys.enc.secret.0.0, idx as usize, enc_gen)?
            }
        };
        Ok(Leg {
            sender: AccountPublicKey::from_affine(sender)?,
            receiver: AccountPublicKey::from_affine(receiver)?,
            asset_id,
            amount,
        })
    }

    pub fn decrypt_with_randomness(
        &self,
        role: LegRole,
        keys: &AccountKeys,
    ) -> Result<(Leg, LegEncryptionRandomness), Error> {
        let enc_key_gen = dart_gens().enc_key_gen();
        let enc_gen = dart_gens().leg_asset_value_gen();
        let (rand, leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, &keys.enc)?;
        let (sender, receiver, asset_id, amount) = leg_enc.decrypt_given_r_checked(
            rand,
            enc_key_gen,
            enc_gen,
            keys.acct.public.get_affine()?,
            role.is_sender(),
        )?;
        Ok((
            Leg {
                sender: AccountPublicKey::from_affine(sender)?,
                receiver: AccountPublicKey::from_affine(receiver)?,
                asset_id,
                amount,
            },
            LegEncryptionRandomness::new(rand)?,
        ))
    }

    pub fn decrypt_with_randomness_checked(
        &self,
        role: LegRole,
        keys: &EncryptionKeyPair,
        account_pk: &AccountPublicKey,
    ) -> Result<(Leg, LegEncryptionRandomness), Error> {
        let enc_key_gen = dart_gens().enc_key_gen();
        let enc_gen = dart_gens().leg_asset_value_gen();
        let (rand, leg_enc, is_sender) = self.bp_decrypt_randomness_and_leg(role, keys)?;
        let pk = account_pk.get_affine()?;
        let (sender, receiver, asset_id, amount) =
            leg_enc.decrypt_given_r_checked(rand, enc_key_gen, enc_gen, pk, is_sender)?;
        Ok((
            Leg {
                sender: AccountPublicKey::from_affine(sender)?,
                receiver: AccountPublicKey::from_affine(receiver)?,
                asset_id,
                amount,
            },
            LegEncryptionRandomness::new(rand)?,
        ))
    }
}

/// The sender affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::AffirmAsSenderTxnProof<ACCOUNT_TREE_L, C::F0, C::F1, C::P0, C::P1>,
    >,
}

impl<C: CurveTreeConfig> core::fmt::Debug for SenderAffirmationProof<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SenderAffirmationProof")
            .field("leg_ref", &self.leg_ref)
            .field("root_block", &self.root_block)
            .field(
                "updated_account_state_commitment",
                &self.updated_account_state_commitment,
            )
            .field("nullifier", &self.nullifier)
            .field("proof", &self.proof)
            .finish()
    }
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderAffirmationProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the sender affirmation.
        let state_change = account_asset.get_sender_affirm_state(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root_node()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsSenderTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for sender affirmation proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for SenderAffirmationProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}

/// The receiver affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct ReceiverAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::AffirmAsReceiverTxnProof<ACCOUNT_TREE_L, C::F0, C::F1, C::P0, C::P1>,
    >,
}

impl<C: CurveTreeConfig> core::fmt::Debug for ReceiverAffirmationProof<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ReceiverAffirmationProof")
            .field("leg_ref", &self.leg_ref)
            .field("root_block", &self.root_block)
            .field(
                "updated_account_state_commitment",
                &self.updated_account_state_commitment,
            )
            .field("nullifier", &self.nullifier)
            .field("proof", &self.proof)
            .finish()
    }
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> ReceiverAffirmationProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the receiver affirmation.
        let state_change = account_asset.get_receiver_affirm_state(account)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root_node()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsReceiverTxnProof::new(
            rng,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for receiver affirmation proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for ReceiverAffirmationProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}

/// The proof for claiming received assets in the Dart BP protocol.
#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct ReceiverClaimProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::ClaimReceivedTxnProof<ACCOUNT_TREE_L, C::F0, C::F1, C::P0, C::P1>,
    >,
}

impl<C: CurveTreeConfig> core::fmt::Debug for ReceiverClaimProof<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ReceiverClaimProof")
            .field("leg_ref", &self.leg_ref)
            .field("root_block", &self.root_block)
            .field(
                "updated_account_state_commitment",
                &self.updated_account_state_commitment,
            )
            .field("nullifier", &self.nullifier)
            .field("proof", &self.proof)
            .finish()
    }
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> ReceiverClaimProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for claiming received assets.
        let state_change = account_asset.get_state_for_claiming_received(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root_node()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::ClaimReceivedTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for receiver claim proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for ReceiverClaimProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}

/// Sender counter update proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderCounterUpdateProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::SenderCounterUpdateTxnProof<ACCOUNT_TREE_L, C::F0, C::F1, C::P0, C::P1>,
    >,
}

impl<C: CurveTreeConfig> core::fmt::Debug for SenderCounterUpdateProof<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SenderCounterUpdateProof")
            .field("leg_ref", &self.leg_ref)
            .field("root_block", &self.root_block)
            .field(
                "updated_account_state_commitment",
                &self.updated_account_state_commitment,
            )
            .field("nullifier", &self.nullifier)
            .field("proof", &self.proof)
            .finish()
    }
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderCounterUpdateProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for decreasing the counter.
        let state_change = account_asset.get_state_for_decreasing_counter(account)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root_node()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderCounterUpdateTxnProof::new(
            rng,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for sender counter update proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for SenderCounterUpdateProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}

/// Sender reversal proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderReversalProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::SenderReverseTxnProof<ACCOUNT_TREE_L, C::F0, C::F1, C::P0, C::P1>,
    >,
}

impl<C: CurveTreeConfig> core::fmt::Debug for SenderReversalProof<C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SenderReversalProof")
            .field("leg_ref", &self.leg_ref)
            .field("root_block", &self.root_block)
            .field(
                "updated_account_state_commitment",
                &self.updated_account_state_commitment,
            )
            .field("nullifier", &self.nullifier)
            .field("proof", &self.proof)
            .finish()
    }
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderReversalProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for reversing the send.
        let state_change = account_asset.get_state_for_reversing_send(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root_node()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderReverseTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for sender reversal proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for SenderReversalProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}

/// Mediator affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct MediatorAffirmationProof {
    pub leg_ref: LegRef,
    pub accept: bool,
    pub key_index: MediatorId,

    proof: WrappedCanonical<bp_leg::MediatorTxnProof<PallasA>>,
}

impl MediatorAffirmationProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        asset_id: AssetId,
        leg_enc: &LegEncrypted,
        mediator_sk: &EncryptionKeyPair,
        key_index: MediatorId,
        accept: bool,
    ) -> Result<Self, Error> {
        let ctx = leg_ref.context();
        let proof = bp_leg::MediatorTxnProof::new(
            rng,
            leg_enc.decode()?,
            asset_id,
            mediator_sk.secret.0.0,
            accept,
            key_index as usize,
            ctx.as_bytes(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            accept,
            key_index,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify(&self, leg_enc: &LegEncrypted) -> Result<(), Error> {
        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            leg_enc.decode()?,
            self.accept,
            self.key_index as usize,
            ctx.as_bytes(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok(())
    }
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
