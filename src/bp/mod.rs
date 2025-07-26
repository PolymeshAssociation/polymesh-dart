use core::marker::PhantomData;
#[cfg(feature = "std")]
use std::collections::HashMap;

use codec::{Decode, Encode, MaxEncodedLen};
use curve_tree_relations::curve_tree::Root;
use dock_crypto_utils::concat_slices;
use dock_crypto_utils::hashing_utils::affine_group_elem_from_try_and_incr;
use polymesh_dart_bp::account::AccountCommitmentKeyTrait;
use scale_info::TypeInfo;

use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{format, string::String, vec::Vec};
use blake2::{Blake2b512, Blake2s256};
use rand_core::{CryptoRng, RngCore, SeedableRng as _};

use bounded_collections::{BoundedVec, ConstU32, Get};

use digest::Digest;
use dock_crypto_utils::commitment::PedersenCommitmentKey;
use polymesh_dart_bp::{account as bp_account, keys as bp_keys, leg as bp_leg};
use polymesh_dart_common::{LegId, MEMO_MAX_LENGTH, SETTLEMENT_MAX_LEGS, SettlementId};

pub mod encode;
pub use encode::{CompressedAffine, WrappedCanonical};

use crate::curve_tree::*;
use crate::*;

pub trait DartLimits: Clone + core::fmt::Debug {
    /// The maximum number of legs in a settlement.
    type MaxSettlementLegs: Get<u32> + Clone + core::fmt::Debug;

    /// The maximum settlement memo length.
    type MaxSettlementMemoLength: Get<u32> + Clone + core::fmt::Debug;
}

impl DartLimits for () {
    type MaxSettlementLegs = ConstU32<SETTLEMENT_MAX_LEGS>;
    type MaxSettlementMemoLength = ConstU32<MEMO_MAX_LENGTH>;
}

pub type LeafIndex = u64;
pub type TreeIndex = u8;
pub type NodeLevel = u8;
pub type NodeIndex = LeafIndex;
pub type ChildIndex = LeafIndex;
pub type SettlementHash = [u8; 32];

pub type PallasParameters = ark_pallas::PallasConfig;
pub type VestaParameters = ark_vesta::VestaConfig;
pub type PallasA = ark_pallas::Affine;
pub type PallasScalar = <PallasA as AffineRepr>::ScalarField;

type BPAccountState = bp_account::AccountState<PallasA>;
type BPAccountStateCommitment = bp_account::AccountStateCommitment<PallasA>;

/// Constants that are hashed to generate the generators for the Dart BP protocol.
pub const DART_GEN_DOMAIN: &'static [u8] = b"polymesh-dart-generators";
pub const DART_GEN_ACCOUNT_KEY: &'static [u8] = b"polymesh-dart-account-key";
pub const DART_GEN_ASSET_KEY: &'static [u8] = b"polymesh-dart-asset-key";
pub const DART_GEN_ENC_KEY: &'static [u8] = b"polymesh-dart-pk-enc";

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    pub static ref DART_GENS: DartBPGenerators = DartBPGenerators::new(DART_GEN_DOMAIN);
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
    pub randomness_gen: PallasA,
}

impl AccountCommitmentKey {
    /// Create a new account commitment key
    pub fn new<D: Digest>(label: &[u8]) -> Self {
        let sk_gen =
            affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![label, b" : sk_gen"]);
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
        let randomness_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : randomness_gen"
        ]);

        Self {
            sk_gen,
            balance_gen,
            counter_gen,
            asset_id_gen,
            rho_gen,
            randomness_gen,
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

    fn randomness_gen(&self) -> PallasA {
        self.randomness_gen
    }
}

#[derive(Clone, Copy, Debug, Encode, Decode, PartialEq, Eq, CanonicalSerialize)]
pub struct AssetCommitmentKey {
    #[codec(encoded_as = "CompressedAffine")]
    pub is_mediator_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    pub asset_id_gen: PallasA,
}

impl AssetCommitmentKey {
    /// Create a new asset commitment key
    pub fn new<D: Digest>(label: &[u8]) -> Self {
        let is_mediator_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : is_mediator_gen"
        ]);
        let asset_id_gen = affine_group_elem_from_try_and_incr::<PallasA, D>(&concat_slices![
            label,
            b" : asset_id_gen"
        ]);

        Self {
            is_mediator_gen,
            asset_id_gen,
        }
    }
}

/// The generators for the Dart BP protocol.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq)]
pub struct DartBPGenerators {
    #[codec(encoded_as = "CompressedAffine")]
    sig_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    enc_gen: PallasA,
    account_comm_key: AccountCommitmentKey,
    asset_comm_key: AssetCommitmentKey,
    #[codec(encoded_as = "CompressedAffine")]
    enc_sig_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    leg_asset_value_gen: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    ped_comm_key_g: PallasA,
    #[codec(encoded_as = "CompressedAffine")]
    ped_comm_key_h: PallasA,
}

impl DartBPGenerators {
    /// Creates a new instance of `DartBPGenerators` by generating the necessary generators.
    pub fn new(label: &[u8]) -> Self {
        let sig_gen = affine_group_elem_from_try_and_incr::<PallasA, Blake2b512>(&concat_slices![
            label,
            b" : sig_gen"
        ]);
        // HACK: The sender affirmation fails if this isn't the same.
        //let pk_enc_g = PallasA::rand(&mut rng);
        let enc_gen = sig_gen;

        let account_comm_key = AccountCommitmentKey::new::<Blake2b512>(DART_GEN_ACCOUNT_KEY);

        let asset_comm_key = AssetCommitmentKey::new::<Blake2b512>(DART_GEN_ASSET_KEY);

        // HACK: The sender affirmation fails if this isn't the same.
        //let leg_g = PallasA::rand(&mut rng);
        let enc_sig_gen = enc_gen;
        let leg_asset_value_gen =
            affine_group_elem_from_try_and_incr::<PallasA, Blake2b512>(&concat_slices![
                label,
                b" : leg_asset_value_gen"
            ]);

        let ped_comm_key =
            PedersenCommitmentKey::<PallasA>::new::<Blake2b512>(b"polymesh-dart-comm-key");

        Self {
            sig_gen,
            enc_gen,
            account_comm_key,
            asset_comm_key,
            enc_sig_gen,
            leg_asset_value_gen,
            ped_comm_key_g: ped_comm_key.g,
            ped_comm_key_h: ped_comm_key.h,
        }
    }

    /// Returns the generators for account state commitments.
    pub fn account_comm_key(&self) -> AccountCommitmentKey {
        self.account_comm_key
    }

    /// Returns the generators for asset state commitments.
    pub fn asset_comm_g(&self) -> [PallasA; 2] {
        [
            self.asset_comm_key.is_mediator_gen,
            self.asset_comm_key.asset_id_gen,
        ]
    }

    pub fn sig_gen(&self) -> PallasA {
        self.sig_gen
    }

    pub fn enc_gen(&self) -> PallasA {
        self.enc_gen
    }

    pub fn enc_sig_gen(&self) -> PallasA {
        self.enc_sig_gen
    }

    pub fn leg_asset_value_gen(&self) -> PallasA {
        self.leg_asset_value_gen
    }

    pub fn ped_comm_key(&self) -> PedersenCommitmentKey<PallasA> {
        PedersenCommitmentKey {
            g: self.ped_comm_key_g,
            h: self.ped_comm_key_h,
        }
    }
}

pub trait AccountStateUpdate {
    fn account_state_commitment(&self) -> AccountStateCommitment;
    fn nullifier(&self) -> AccountStateNullifier;
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

#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    TypeInfo,
    Debug,
    CanonicalSerialize,
    CanonicalDeserialize,
    PartialEq,
    Eq,
    Hash,
)]
pub struct EncryptionPublicKey(CompressedAffine);

impl From<AccountPublicKey> for EncryptionPublicKey {
    fn from(account_pk: AccountPublicKey) -> Self {
        EncryptionPublicKey(account_pk.0)
    }
}

impl EncryptionPublicKey {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    pub fn from_bp_key(pk: bp_keys::EncKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    pub fn get_bp_key(&self) -> Result<bp_keys::EncKey<PallasA>, Error> {
        Ok(bp_keys::EncKey(self.get_affine()?))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EncryptionSecretKey(bp_keys::DecKey<PallasA>);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EncryptionKeyPair {
    pub public: EncryptionPublicKey,
    secret: EncryptionSecretKey,
}

impl EncryptionKeyPair {
    /// Generates a new set of encryption keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let (enc, enc_pk) = bp_keys::keygen_enc(rng, dart_gens().enc_gen());
        Ok(Self {
            public: EncryptionPublicKey::from_bp_key(enc_pk)?,
            secret: EncryptionSecretKey(enc),
        })
    }
}

#[derive(Copy, Clone, MaxEncodedLen, Encode, Decode, TypeInfo, Debug, PartialEq, Eq, Hash)]
pub struct AccountPublicKey(CompressedAffine);

impl AccountPublicKey {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    pub fn from_bp_key(pk: bp_keys::VerKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    pub fn get_bp_key(&self) -> Result<bp_keys::VerKey<PallasA>, Error> {
        Ok(bp_keys::VerKey(self.get_affine()?))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AccountSecretKey(bp_keys::SigKey<PallasA>);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AccountKeyPair {
    pub public: AccountPublicKey,
    secret: AccountSecretKey,
}

impl AccountKeyPair {
    /// Generates a new set of account keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let (account, account_pk) = bp_keys::keygen_sig(rng, dart_gens().sig_gen());
        Ok(Self {
            public: AccountPublicKey::from_bp_key(account_pk)?,
            secret: AccountSecretKey(account),
        })
    }

    pub fn account_state<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        asset_id: AssetId,
    ) -> Result<AccountState, Error> {
        Ok(AccountState(BPAccountState::new(
            rng,
            self.secret.0.0,
            asset_id,
        )?))
    }
}

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
pub struct AccountPublicKeys {
    pub enc: EncryptionPublicKey,
    pub acct: AccountPublicKey,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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
    ) -> Result<AccountAssetState, Error> {
        AccountAssetState::new(rng, self, asset_id)
    }

    /// Returns the public keys for the account.
    pub fn public_keys(&self) -> AccountPublicKeys {
        AccountPublicKeys {
            enc: self.enc.public,
            acct: self.acct.public,
        }
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct AccountState(BPAccountState);

impl AccountState {
    pub fn commitment(&self) -> Result<AccountStateCommitment, Error> {
        AccountStateCommitment::from_affine(self.0.commit(dart_gens().account_comm_key())?.0)
    }
}

#[derive(Copy, Clone, MaxEncodedLen, Encode, Decode, TypeInfo, Debug, PartialEq, Eq, Hash)]
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
pub struct AccountStateCommitment(CompressedAffine);

impl AccountStateCommitment {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    pub fn as_leaf_value(&self) -> Result<LeafValue<PallasParameters>, Error> {
        Ok(LeafValue(self.get_affine()?))
    }

    pub fn as_commitment(&self) -> Result<BPAccountStateCommitment, Error> {
        Ok(bp_account::AccountStateCommitment(self.get_affine()?))
    }
}

#[derive(Clone, Debug)]
pub struct AccountAssetState {
    pub account: AccountKeys,
    pub asset_id: AssetId,
    pub current_state: AccountState,
    pub current_state_commitment: AccountStateCommitment,
    pub current_tx_id: u64,
    pub pending_state: Option<AccountState>,
}

impl AccountAssetState {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeys,
        asset_id: AssetId,
    ) -> Result<Self, Error> {
        let current_state = account.acct.account_state(rng, asset_id)?;
        let current_state_commitment = current_state.commitment()?;
        Ok(Self {
            account: *account,
            asset_id,
            current_state,
            current_state_commitment,
            current_tx_id: 0,
            pending_state: None,
        })
    }

    pub fn mint<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> Result<AccountState, Error> {
        let state = AccountState(self.current_state.0.get_state_for_mint(rng, amount)?);
        self._set_pending_state(state.clone());
        Ok(state)
    }

    pub fn get_sender_affirm_state<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> Result<AccountState, Error> {
        let state = AccountState(self.current_state.0.get_state_for_send(rng, amount)?);
        self._set_pending_state(state.clone());
        Ok(state)
    }

    pub fn get_receiver_affirm_state<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
    ) -> Result<AccountState, Error> {
        let state = AccountState(self.current_state.0.get_state_for_receive(rng));
        self._set_pending_state(state.clone());
        Ok(state)
    }

    pub fn get_state_for_claiming_received<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> Result<AccountState, Error> {
        let state = AccountState(
            self.current_state
                .0
                .get_state_for_claiming_received(rng, amount)?,
        );
        self._set_pending_state(state.clone());
        Ok(state)
    }

    pub fn get_state_for_reversing_send<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> Result<AccountState, Error> {
        let state = AccountState(
            self.current_state
                .0
                .get_state_for_reversing_send(rng, amount)?,
        );
        self._set_pending_state(state.clone());
        Ok(state)
    }

    pub fn get_state_for_decreasing_counter<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
    ) -> Result<AccountState, Error> {
        let state = AccountState(
            self.current_state
                .0
                .get_state_for_decreasing_counter(rng, None)?,
        );
        self._set_pending_state(state.clone());
        Ok(state)
    }

    fn _set_pending_state(&mut self, state: AccountState) {
        self.pending_state = Some(state);
    }

    pub fn commit_pending_state(&mut self) -> Result<bool, Error> {
        match self.pending_state.take() {
            Some(pending_state) => {
                self.current_state = pending_state;
                self.current_state_commitment = self.current_state.commitment()?;
                self.current_tx_id += 1;
                Ok(true)
            }
            None => Ok(false),
        }
    }
}

/// Represents the state of an asset in the Dart BP protocol.
#[derive(Clone, Debug, Encode, Decode, TypeInfo)]
pub struct AssetState {
    asset_id: AssetId,
    is_mediator: bool,
    pk: EncryptionPublicKey,
}

impl AssetState {
    /// Creates a new asset state with the given asset ID, mediator status, and public key.
    pub fn new(asset_id: AssetId, is_mediator: bool, pk: EncryptionPublicKey) -> Self {
        Self {
            asset_id,
            is_mediator,
            pk,
        }
    }

    /// Changes the auditor or mediator for the asset.
    pub fn change_auditor(&mut self, is_mediator: bool, pk: EncryptionPublicKey) {
        self.is_mediator = is_mediator;
        self.pk = pk;
    }

    /// Given commitment key `leaf_comm_key`, the leaf is `leaf_comm_key[0] * role + leaf_comm_key[1] * asset_id + pk`
    /// where `role` equals 1 if `pk` is the public key of mediator else its 0.A
    pub fn commitment(&self) -> Result<AssetStateCommitment, Error> {
        let leaf_comm_key = dart_gens().asset_comm_g();
        let comm = if self.is_mediator {
            leaf_comm_key[0]
        } else {
            <PallasA as AffineRepr>::zero()
        };
        AssetStateCommitment::from_affine(
            (comm
                + (leaf_comm_key[1] * PallasScalar::from(self.asset_id))
                + self.pk.get_affine()?)
            .into_affine(),
        )
    }
}

/// Represents the commitment of an asset state in the Dart BP protocol.
#[derive(Copy, Clone, MaxEncodedLen, Encode, Decode, TypeInfo, Debug, PartialEq, Eq)]
pub struct AssetStateCommitment(CompressedAffine);

impl AssetStateCommitment {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    pub fn as_leaf_value(&self) -> Result<LeafValue<PallasParameters>, Error> {
        Ok(LeafValue(self.get_affine()?))
    }
}

/// Represents a tree of asset states in the Dart BP protocol.
#[cfg(feature = "std")]
pub struct AssetCurveTree {
    pub tree: FullCurveTree<ASSET_TREE_L>,
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
        let leaf = state.commitment()?;

        // Update or insert the asset state.
        use std::collections::hash_map::Entry;
        match self.assets.entry(asset_id) {
            Entry::Occupied(mut entry) => {
                let (index, existing_state) = entry.get_mut();
                *existing_state = state;
                let index = *index;
                // Update the leaf in the curve tree.
                self.tree.update(leaf.as_leaf_value()?, index)?;

                Ok(index)
            }
            Entry::Vacant(entry) => {
                let index = self.tree.insert(leaf.as_leaf_value()?)?;
                entry.insert((index, state));

                Ok(index)
            }
        }
    }

    pub fn get_asset_state_path(&self, asset_id: AssetId) -> Option<CurveTreePath<ASSET_TREE_L>> {
        let (leaf_index, _) = self.assets.get(&asset_id)?;
        self.tree.get_path_to_leaf_index(*leaf_index).ok()
    }

    pub fn params(&self) -> &CurveTreeParameters {
        self.tree.params()
    }

    pub fn root_node(&self) -> Result<CurveTreeRoot<ASSET_TREE_L>, Error> {
        self.tree.root_node()
    }
}

/// Account asset registration proof.  Report section 5.1.3 "Account Registration".
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct AccountAssetRegistrationProof {
    pub account: AccountPublicKey,
    pub account_state_commitment: AccountStateCommitment,
    pub asset_id: AssetId,

    proof: WrappedCanonical<bp_account::RegTxnProof<PallasA>>,
}

impl AccountAssetRegistrationProof {
    /// Generate a new account state for an asset and a registration proof for it.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeys,
        asset_id: AssetId,
        ctx: &[u8],
    ) -> Result<(Self, AccountAssetState), Error> {
        let account_state = account.init_asset_state(rng, asset_id)?;
        let account_state_commitment = account_state.current_state_commitment;
        let proof = bp_account::RegTxnProof::new(
            rng,
            account.acct.public.get_affine()?,
            &account_state.current_state.0,
            account_state_commitment.as_commitment()?,
            ctx,
            dart_gens().account_comm_key(),
            dart_gens().sig_gen(),
        )?;
        Ok((
            Self {
                account: account.acct.public,
                account_state_commitment,
                asset_id,
                proof: WrappedCanonical::wrap(&proof)?,
            },
            account_state,
        ))
    }

    /// Verifies the account asset registration proof against the provided public key, asset ID, and account state commitment.
    pub fn verify(&self, ctx: &[u8]) -> Result<(), Error> {
        let proof = self.proof.decode()?;
        proof.verify(
            &self.account.get_affine()?,
            self.asset_id,
            &self.account_state_commitment.as_commitment()?,
            ctx,
            dart_gens().account_comm_key(),
            dart_gens().sig_gen(),
        )?;
        Ok(())
    }
}

/// Asset minting proof.  Report section 5.1.4 "Increase Asset Supply".
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct AssetMintingProof {
    // Public inputs.
    pub pk: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    // proof
    proof: WrappedCanonical<
        bp_account::MintTxnProof<
            ACCOUNT_TREE_L,
            <PallasParameters as CurveConfig>::ScalarField,
            <VestaParameters as CurveConfig>::ScalarField,
            PallasParameters,
            VestaParameters,
        >,
    >,
}

impl AssetMintingProof {
    /// Generate a new asset minting proof.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
        amount: Balance,
    ) -> Result<Self, Error> {
        // Generate a new minting state for the account asset.
        let mint_account_state = account_asset.mint(rng, amount)?;
        let mint_account_commitment = mint_account_state.commitment()?;

        let pk = account_asset.account.acct.public;
        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.as_leaf_value()?)?;

        let root = tree_lookup.root_node()?;

        let (proof, nullifier) = bp_account::MintTxnProof::new(
            rng,
            pk.get_affine()?,
            amount,
            current_account_state,
            &mint_account_state.0,
            mint_account_commitment.as_commitment()?,
            current_account_path,
            b"",
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().sig_gen(),
        )?;
        Ok(Self {
            pk,
            asset_id: account_asset.asset_id,
            amount,
            root,
            updated_account_state_commitment: mint_account_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for asset minting proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let root = self.root.decode()?;
        let proof = self.proof.decode()?;
        proof.verify_with_rng(
            self.pk.get_affine()?,
            self.asset_id,
            self.amount,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            &root,
            b"",
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().sig_gen(),
            rng,
        )?;
        Ok(())
    }
}

impl AccountStateUpdate for AssetMintingProof {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }
}

/// Represents the auditor or mediator in a leg of the Dart BP protocol.
#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
pub enum AuditorOrMediator {
    Mediator(AccountPublicKeys),
    Auditor(EncryptionPublicKey),
}

impl AuditorOrMediator {
    pub fn mediator(pk: &AccountPublicKeys) -> Self {
        Self::Mediator(*pk)
    }

    pub fn auditor(pk: &EncryptionPublicKey) -> Self {
        Self::Auditor(*pk)
    }

    pub fn get_keys(
        &self,
    ) -> (
        EncryptionPublicKey,
        Option<AccountPublicKey>,
        Option<EncryptionPublicKey>,
    ) {
        match self {
            AuditorOrMediator::Mediator(pk) => (pk.enc, Some(pk.acct), None),
            AuditorOrMediator::Auditor(pk) => (*pk, None, Some(*pk)),
        }
    }
}

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
pub enum SettlementRef {
    /// ID based reference.
    ID(#[codec(compact)] SettlementId),
    /// Hash based reference.
    Hash(SettlementHash),
}

impl From<SettlementId> for SettlementRef {
    fn from(id: SettlementId) -> Self {
        SettlementRef::ID(id)
    }
}

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
pub struct LegRef {
    /// The settlement reference.
    pub settlement: SettlementRef,
    /// The leg ID within the settlement.
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
pub enum LegRole {
    Sender,
    Receiver,
    Auditor,
    Mediator,
}

/// The decrypted leg details in the Dart BP protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leg(bp_leg::Leg<PallasA>);

impl Leg {
    pub fn new(
        sender: AccountPublicKey,
        receiver: AccountPublicKey,
        mediator: Option<AccountPublicKey>,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<Self, Error> {
        let leg = bp_leg::Leg::new(
            sender.get_affine()?,
            receiver.get_affine()?,
            mediator.map(|m| m.get_affine()).transpose()?,
            amount,
            asset_id,
        )?;
        Ok(Self(leg))
    }

    pub fn encrypt<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ephemeral_key: EphemeralSkEncryption,
        pk_e: &EncryptionPublicKey,
    ) -> Result<(LegEncrypted, LegEncryptionRandomness), Error> {
        let (leg_enc, leg_enc_rand) = self.0.encrypt(
            rng,
            &pk_e.get_affine()?,
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
        );
        Ok((
            LegEncrypted {
                leg_enc,
                ephemeral_key,
            },
            LegEncryptionRandomness(leg_enc_rand),
        ))
    }

    pub fn sender(&self) -> Result<AccountPublicKey, Error> {
        AccountPublicKey::from_affine(self.0.pk_s)
    }

    pub fn receiver(&self) -> Result<AccountPublicKey, Error> {
        AccountPublicKey::from_affine(self.0.pk_r)
    }

    pub fn mediator(&self) -> Result<Option<AccountPublicKey>, Error> {
        self.0
            .pk_m
            .map(|m| AccountPublicKey::from_affine(m))
            .transpose()
    }

    pub fn asset_id(&self) -> AssetId {
        self.0.asset_id
    }

    pub fn amount(&self) -> Balance {
        self.0.amount
    }
}

/// A helper type to build the encrypted leg and its proof in the Dart BP protocol.
pub struct LegBuilder {
    pub sender: AccountPublicKeys,
    pub receiver: AccountPublicKeys,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub mediator: AuditorOrMediator,
}

impl LegBuilder {
    /// Creates a new leg with the given sender, receiver, asset ID, amount, and optional mediator.
    pub fn new(
        sender: AccountPublicKeys,
        receiver: AccountPublicKeys,
        asset_id: AssetId,
        amount: Balance,
        mediator: AuditorOrMediator,
    ) -> Self {
        Self {
            sender,
            receiver,
            asset_id,
            amount,
            mediator,
        }
    }

    pub fn encryt_and_prove<R: RngCore + CryptoRng>(
        self,
        rng: &mut R,
        ctx: &[u8],
        asset_tree: &impl CurveTreeLookup<ASSET_TREE_L>,
    ) -> Result<SettlementLegProof, Error> {
        let (mediator_enc, mediator_acct, auditor_enc) = self.mediator.get_keys();
        let leg = Leg::new(
            self.sender.acct,
            self.receiver.acct,
            mediator_acct,
            self.asset_id,
            self.amount,
        )?;
        let (ephemeral_key, eph_rand, pk_e) =
            EphemeralSkEncryption::new(rng, self.sender.enc, self.receiver.enc, mediator_enc)?;
        let (leg_enc, leg_enc_rand) = leg.encrypt(rng, ephemeral_key, &pk_e)?;

        let leg_proof = SettlementLegProof::new(
            rng,
            leg,
            leg_enc,
            &leg_enc_rand,
            eph_rand,
            pk_e,
            auditor_enc,
            ctx,
            asset_tree,
        )?;

        Ok(leg_proof)
    }
}

pub struct SettlementBuilder<T: DartLimits = ()> {
    memo: Vec<u8>,
    legs: Vec<LegBuilder>,
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

    pub fn encryt_and_prove<R: RngCore + CryptoRng>(
        self,
        rng: &mut R,
        asset_tree: impl CurveTreeLookup<ASSET_TREE_L>,
    ) -> Result<SettlementProof<T>, Error> {
        let memo = BoundedVec::try_from(self.memo)
            .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        let root = asset_tree.root_node()?;

        let mut legs = Vec::with_capacity(self.legs.len());

        for (idx, leg_builder) in self.legs.into_iter().enumerate() {
            let ctx = (&memo, idx as u8).encode();
            let leg_proof = leg_builder.encryt_and_prove(rng, &ctx, &asset_tree)?;
            legs.push(leg_proof);
        }

        let legs =
            BoundedVec::try_from(legs).map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        Ok(SettlementProof { memo, root, legs })
    }
}

#[derive(Clone, Encode, Decode, Debug, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct SettlementProof<T: DartLimits> {
    pub memo: BoundedVec<u8, T::MaxSettlementMemoLength>,
    root: CurveTreeRoot<ASSET_TREE_L>,

    pub legs: BoundedVec<SettlementLegProof, T::MaxSettlementLegs>,
}

impl<T: DartLimits> PartialEq for SettlementProof<T> {
    fn eq(&self, other: &Self) -> bool {
        self.memo == other.memo && self.root == other.root && self.legs == other.legs
    }
}

impl<T: DartLimits> Eq for SettlementProof<T> {}

impl<T: DartLimits> SettlementProof<T> {
    pub fn hash(&self) -> SettlementHash {
        let mut hasher = Blake2s256::new();
        let data = self.encode();
        hasher.update(&data);
        hasher.finalize().into()
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        asset_tree: impl ValidateCurveTreeRoot<ASSET_TREE_L>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Validate the root of the curve tree.
        if !asset_tree.validate_root(&self.root) {
            log::error!("Invalid root for settlement proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let root = self.root.decode()?;
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
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct SettlementLegProof {
    leg_enc: WrappedCanonical<LegEncrypted>,

    proof: WrappedCanonical<
        bp_leg::SettlementTxnProof<
            ASSET_TREE_L,
            <PallasParameters as CurveConfig>::ScalarField,
            <VestaParameters as CurveConfig>::ScalarField,
            PallasParameters,
            VestaParameters,
        >,
    >,
}

impl SettlementLegProof {
    pub(crate) fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg: Leg,
        leg_enc: LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        eph_rand: PallasScalar,
        pk_e: EncryptionPublicKey,
        auditor_enc: Option<EncryptionPublicKey>,
        ctx: &[u8],
        asset_tree: &impl CurveTreeLookup<ASSET_TREE_L>,
    ) -> Result<Self, Error> {
        let asset_path = asset_tree.get_path_to_leaf_index(leg.asset_id() as LeafIndex)?;

        let proof = bp_leg::SettlementTxnProof::new(
            rng,
            leg.0,
            leg_enc.leg_enc.clone(),
            leg_enc_rand.0.clone(),
            leg_enc.ephemeral_key.enc.clone(),
            eph_rand,
            pk_e.get_affine()?,
            auditor_enc.map(|m| m.get_affine()).transpose()?,
            asset_path,
            ctx,
            asset_tree.params(),
            &dart_gens().asset_comm_g(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
            &dart_gens().ped_comm_key(),
        )?;

        Ok(Self {
            leg_enc: WrappedCanonical::wrap(&leg_enc)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn leg_enc(&self) -> Result<LegEncrypted, Error> {
        self.leg_enc.decode()
    }

    pub fn has_mediator(&self) -> Result<bool, Error> {
        let leg_enc = self.leg_enc.decode()?;
        Ok(leg_enc.leg_enc.ct_m.is_some())
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        ctx: &[u8],
        root: &Root<ASSET_TREE_L, 1, PallasParameters, VestaParameters>,
        params: &CurveTreeParameters,
        rng: &mut R,
    ) -> Result<(), Error> {
        let leg_enc = self.leg_enc.decode()?;
        let pk_e = leg_enc.ephemeral_key.pk_e;
        log::debug!("Verify leg: {:?}", leg_enc.leg_enc);
        let proof = self.proof.decode()?;
        proof.verify_with_rng(
            leg_enc.leg_enc.clone(),
            leg_enc.ephemeral_key.enc.clone(),
            pk_e.get_affine()?,
            &root,
            ctx,
            params,
            &dart_gens().asset_comm_g(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
            &dart_gens().ped_comm_key(),
            rng,
        )?;
        Ok(())
    }
}

/// Represents a hashed settlement proof in the Dart BP protocol.
///
/// This allows building the settlement off-chain and collecting the leg affirmations
/// before submitting the settlement to the chain.
#[derive(Clone, Encode, Decode, Debug, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct HashedSettlementProof<T: DartLimits = ()> {
    /// The settlement proof containing the memo, root, and legs.
    pub settlement: SettlementProof<T>,
    /// The hash of the settlement, used to tie the leg affirmations to this settlement.
    pub hash: SettlementHash,
}

impl<T: DartLimits> PartialEq for HashedSettlementProof<T> {
    fn eq(&self, other: &Self) -> bool {
        self.settlement == other.settlement && self.hash == other.hash
    }
}

impl<T: DartLimits> Eq for HashedSettlementProof<T> {}

/// Counts of the legs and sender/receiver affirmations in a batched settlement.
#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct BatchedSettlementCounts {
    pub leg_count: u32,
    pub sender_count: u64,
    pub receiver_count: u64,
}

/// Represents the affirmation proofs for each leg in a settlement.
/// This includes the sender, and receiver affirmation proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct BatchedSettlementLegAffirmations {
    /// The sender's affirmation proof.
    pub sender: Option<SenderAffirmationProof>,
    /// The receiver's affirmation proof.
    pub receiver: Option<ReceiverAffirmationProof>,
}

/// A batched settlement proof allows including the sender and receiver affirmation proofs
/// with the settlement creation proof to reduce the number of transactions
/// required to finalize a settlement.
#[derive(Clone, Encode, Decode, Debug, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct BatchedSettlementProof<T: DartLimits = ()> {
    /// The settlement proof containing the memo, root, and legs.
    pub hashed_settlement: HashedSettlementProof<T>,

    /// The leg affirmations for each leg in the settlement.
    pub leg_affirmations: BoundedVec<BatchedSettlementLegAffirmations, T::MaxSettlementLegs>,
}

impl<T: DartLimits> PartialEq for BatchedSettlementProof<T> {
    fn eq(&self, other: &Self) -> bool {
        self.hashed_settlement == other.hashed_settlement
            && self.leg_affirmations == other.leg_affirmations
    }
}

impl<T: DartLimits> Eq for BatchedSettlementProof<T> {}

impl<T: DartLimits> BatchedSettlementProof<T> {
    /// The settlemetn reference using the hash of the settlement.
    pub fn settlement_ref(&self) -> SettlementRef {
        SettlementRef::Hash(self.hashed_settlement.hash)
    }

    /// The settlement creation proof.
    pub fn settlement_proof(&self) -> &SettlementProof<T> {
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

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct EphemeralSkEncryption {
    pub(crate) enc: bp_leg::EphemeralSkEncryption<PallasA>,
    pub(crate) pk_e: EncryptionPublicKey,
}

impl EphemeralSkEncryption {
    pub(crate) fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        sender: EncryptionPublicKey,
        receiver: EncryptionPublicKey,
        mediator: EncryptionPublicKey,
    ) -> Result<(Self, PallasScalar, EncryptionPublicKey), Error> {
        let (ephemeral_key, eph_key_rand, _sk_e, pk_e) =
            bp_leg::EphemeralSkEncryption::new::<_, Blake2b512>(
                rng,
                sender.get_affine()?,
                receiver.get_affine()?,
                mediator.get_affine()?,
                dart_gens().enc_sig_gen(),
                dart_gens().leg_asset_value_gen(),
            )?;
        let pk_e = EncryptionPublicKey::from_bp_key(pk_e)?;
        Ok((
            Self {
                enc: ephemeral_key,
                pk_e,
            },
            eph_key_rand,
            pk_e,
        ))
    }
}

pub struct LegEncryptionRandomness(bp_leg::LegEncryptionRandomness<PallasA>);

/// Represents an encrypted leg in the Dart BP protocol.  Stored onchain.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct LegEncrypted {
    pub(crate) leg_enc: bp_leg::LegEncryption<PallasA>,
    pub(crate) ephemeral_key: EphemeralSkEncryption,
}

impl LegEncrypted {
    pub fn decrypt_sk_e(
        &self,
        role: LegRole,
        keys: &EncryptionKeyPair,
    ) -> Result<EncryptionSecretKey, Error> {
        let sk = keys.secret.0.0;
        let sk_e = match role {
            LegRole::Sender => self
                .ephemeral_key
                .enc
                .decrypt_for_sender::<Blake2b512>(sk)?,
            LegRole::Receiver => self
                .ephemeral_key
                .enc
                .decrypt_for_receiver::<Blake2b512>(sk)?,
            LegRole::Auditor | LegRole::Mediator => self
                .ephemeral_key
                .enc
                .decrypt_for_mediator_or_auditor::<Blake2b512>(sk)?,
        };
        Ok(EncryptionSecretKey(bp_keys::DecKey(sk_e)))
    }

    /// Decrypts the leg using the provided secret key and role.
    pub fn decrypt(&self, role: LegRole, keys: &EncryptionKeyPair) -> Result<Leg, Error> {
        let sk_e = self.decrypt_sk_e(role, keys)?;
        log::debug!("Decrypted sk_e: {:?}", sk_e.0.0);
        let leg = self
            .leg_enc
            .decrypt(&sk_e.0.0, dart_gens().leg_asset_value_gen())?;
        Ok(Leg(leg))
    }
}

/// The sender affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct SenderAffirmationProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::AffirmAsSenderTxnProof<
            ACCOUNT_TREE_L,
            <PallasParameters as CurveConfig>::ScalarField,
            <VestaParameters as CurveConfig>::ScalarField,
            PallasParameters,
            VestaParameters,
        >,
    >,
}

impl SenderAffirmationProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        amount: Balance,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the sender affirmation.
        let new_account_state = account_asset.get_sender_affirm_state(rng, amount)?;
        let new_account_commitment = new_account_state.commitment()?;

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.as_leaf_value()?)?;

        let root = tree_lookup.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsSenderTxnProof::new(
            rng,
            amount,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.as_commitment()?,
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root,
            updated_account_state_commitment: new_account_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for sender affirmation proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let root = self.root.decode()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify_with_rng(
            leg_enc.leg_enc.clone(),
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
            rng,
        )?;
        Ok(())
    }
}

impl AccountStateUpdate for SenderAffirmationProof {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }
}

/// The receiver affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct ReceiverAffirmationProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::AffirmAsReceiverTxnProof<
            ACCOUNT_TREE_L,
            <PallasParameters as CurveConfig>::ScalarField,
            <VestaParameters as CurveConfig>::ScalarField,
            PallasParameters,
            VestaParameters,
        >,
    >,
}

impl ReceiverAffirmationProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the receiver affirmation.
        let new_account_state = account_asset.get_receiver_affirm_state(rng)?;
        let new_account_commitment = new_account_state.commitment()?;

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.as_leaf_value()?)?;

        let root = tree_lookup.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsReceiverTxnProof::new(
            rng,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.as_commitment()?,
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root,
            updated_account_state_commitment: new_account_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for receiver affirmation proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let root = self.root.decode()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify_with_rng(
            leg_enc.leg_enc.clone(),
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
            rng,
        )?;
        Ok(())
    }
}

impl AccountStateUpdate for ReceiverAffirmationProof {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }
}

/// The proof for claiming received assets in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct ReceiverClaimProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::ClaimReceivedTxnProof<
            ACCOUNT_TREE_L,
            <PallasParameters as CurveConfig>::ScalarField,
            <VestaParameters as CurveConfig>::ScalarField,
            PallasParameters,
            VestaParameters,
        >,
    >,
}

impl ReceiverClaimProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        amount: Balance,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Result<Self, Error> {
        // Generate a new account state for claiming received assets.
        let new_account_state = account_asset.get_state_for_claiming_received(rng, amount)?;
        let new_account_commitment = new_account_state.commitment()?;

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.as_leaf_value()?)?;

        let root = tree_lookup.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::ClaimReceivedTxnProof::new(
            rng,
            amount,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.as_commitment()?,
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root,
            updated_account_state_commitment: new_account_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for receiver claim proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let root = self.root.decode()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify_with_rng(
            leg_enc.leg_enc.clone(),
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
            rng,
        )?;
        Ok(())
    }
}

impl AccountStateUpdate for ReceiverClaimProof {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }
}

/// Sender counter update proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct SenderCounterUpdateProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::SenderCounterUpdateTxnProof<
            ACCOUNT_TREE_L,
            <PallasParameters as CurveConfig>::ScalarField,
            <VestaParameters as CurveConfig>::ScalarField,
            PallasParameters,
            VestaParameters,
        >,
    >,
}

impl SenderCounterUpdateProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Result<Self, Error> {
        // Generate a new account state for decreasing the counter.
        let new_account_state = account_asset.get_state_for_decreasing_counter(rng)?;
        let new_account_commitment = new_account_state.commitment()?;

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.as_leaf_value()?)?;

        let root = tree_lookup.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderCounterUpdateTxnProof::new(
            rng,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.as_commitment()?,
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root,
            updated_account_state_commitment: new_account_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for sender counter update proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let root = self.root.decode()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify_with_rng(
            leg_enc.leg_enc.clone(),
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
            rng,
        )?;
        Ok(())
    }
}

impl AccountStateUpdate for SenderCounterUpdateProof {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }
}

/// Sender reversal proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct SenderReversalProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<
        bp_account::SenderReverseTxnProof<
            ACCOUNT_TREE_L,
            <PallasParameters as CurveConfig>::ScalarField,
            <VestaParameters as CurveConfig>::ScalarField,
            PallasParameters,
            VestaParameters,
        >,
    >,
}

impl SenderReversalProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        amount: Balance,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Result<Self, Error> {
        // Generate a new account state for reversing the send.
        let new_account_state = account_asset.get_state_for_reversing_send(rng, amount)?;
        let new_account_commitment = new_account_state.commitment()?;

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.as_leaf_value()?)?;

        let root = tree_lookup.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderReverseTxnProof::new(
            rng,
            amount,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.as_commitment()?,
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root,
            updated_account_state_commitment: new_account_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for sender reversal proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let root = self.root.decode()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify_with_rng(
            leg_enc.leg_enc.clone(),
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_sig_gen(),
            dart_gens().leg_asset_value_gen(),
            rng,
        )?;
        Ok(())
    }
}

impl AccountStateUpdate for SenderReversalProof {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }
}

/// Mediator affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct MediatorAffirmationProof {
    pub leg_ref: LegRef,
    pub accept: bool,

    proof: WrappedCanonical<bp_leg::MediatorTxnProof<PallasA>>,
}

impl MediatorAffirmationProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        eph_sk: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        mediator_sk: &AccountKeyPair,
        accept: bool,
    ) -> Result<Self, Error> {
        let ctx = leg_ref.context();
        let eph_pk = leg_enc.ephemeral_key.pk_e;
        let proof = bp_leg::MediatorTxnProof::new(
            rng,
            leg_enc.leg_enc.clone(),
            eph_sk.0.0,
            eph_pk.get_affine()?,
            mediator_sk.secret.0.0,
            accept,
            ctx.as_bytes(),
            dart_gens().enc_sig_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            accept,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify(&self, leg_enc: &LegEncrypted) -> Result<(), Error> {
        let ctx = self.leg_ref.context();
        let eph_pk = leg_enc.ephemeral_key.pk_e;
        let proof = self.proof.decode()?;
        proof.verify(
            leg_enc.leg_enc.clone(),
            eph_pk.get_affine()?,
            self.accept,
            ctx.as_bytes(),
            dart_gens().enc_sig_gen(),
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
