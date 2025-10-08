#[cfg(feature = "std")]
use std::collections::HashMap;

#[cfg(feature = "parallel")]
use rayon::prelude::*;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::{
    PrimeField,
    field_hashers::{DefaultFieldHasher, HashToField},
};
use ark_serialize::CanonicalSerialize;
use ark_std::vec::Vec;

use blake2::Blake2b512;
use bounded_collections::{BoundedBTreeSet, BoundedVec, ConstU32, Get};
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use digest::Digest;
use rand_core::{CryptoRng, RngCore};

use polymesh_dart_bp::{
    account as bp_account,
    account::AccountCommitmentKeyTrait,
    account_registration, leg as bp_leg,
    poseidon_impls::poseidon_2::{
        Poseidon2Params, params::pallas::get_poseidon2_params_for_2_1_hashing,
    },
};
use polymesh_dart_common::{
    MAX_ACCOUNT_ASSET_REG_PROOFS, MAX_ASSET_AUDITORS, MAX_ASSET_MEDIATORS, MAX_KEYS_PER_REG_PROOF,
    MEMO_MAX_LENGTH, NullifierSkGenCounter, SETTLEMENT_MAX_LEGS,
};

#[cfg(feature = "sqlx")]
pub mod sqlx_impl;

pub mod encode;
pub use encode::{CompressedAffine, WrappedCanonical};

mod leg;
pub use leg::*;

mod keys;
pub use keys::*;

mod fee;
pub use fee::*;

use crate::curve_tree::*;
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
        let balance_gen = hash_to_pallas(
            label, 
            b" : balance_gen"
        ).into_affine();
        let counter_gen = hash_to_pallas(
            label,
            b" : counter_gen"
        ).into_affine();
        let asset_id_gen = hash_to_pallas(
            label,
            b" : asset_id_gen"
        ).into_affine();
        let rho_gen = hash_to_pallas(
            label,
            b" : rho_gen"
        ).into_affine();
        let current_rho_gen = hash_to_pallas(
            label,
            b" : current_rho_gen"
        ).into_affine();
        let randomness_gen = hash_to_pallas(
            label,
            b" : randomness_gen"
        ).into_affine();
        let identity_gen = hash_to_pallas(
            label,
            b" : identity_gen"
        ).into_affine();

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
            hash_to_pallas(
                label,
                b" : sig_key_gen"
            ).into_affine();
        let enc_key_gen =
            hash_to_pallas(
                label,
                b" : enc_key_gen"
            ).into_affine();

        let account_comm_key =
            AccountCommitmentKey::new::<Blake2b512>(DART_GEN_ACCOUNT_KEY, sig_key_gen);

        let leg_asset_value_gen =
            hash_to_pallas(
                label,
                b" : leg_asset_value_gen"
            ).into_affine();

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

    pub fn root(
        &self,
    ) -> Result<CompressedCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>, Error> {
        self.tree.root()
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

/// Batched account asset registration proof.
///
/// This is used to register multiple account/asset pairs in a single proof.
#[derive(Clone, Encode, Decode, Debug, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct BatchedAccountAssetRegistrationProof<T: DartLimits = ()> {
    pub proofs: BoundedVec<AccountAssetRegistrationProof, T::MaxAccountAssetRegProofs>,
}

impl<T: DartLimits> PartialEq for BatchedAccountAssetRegistrationProof<T> {
    fn eq(&self, other: &Self) -> bool {
        self.proofs == other.proofs
    }
}

impl<T: DartLimits> Eq for BatchedAccountAssetRegistrationProof<T> {}

impl<T: DartLimits> BatchedAccountAssetRegistrationProof<T> {
    /// Generate a new batched account asset registration proof.
    #[cfg(feature = "parallel")]
    pub fn new<R: RngCore + CryptoRng + Sync + Send + Clone>(
        rng: &mut R,
        account_assets: &[(AccountKeyPair, AssetId, NullifierSkGenCounter)],
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
    ) -> Result<(Self, Vec<AccountAssetState>), Error> {
        let proofs_and_states = account_assets
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, (account, asset_id, counter)| {
                    AccountAssetRegistrationProof::new(
                        rng,
                        account,
                        *asset_id,
                        *counter,
                        identity,
                        tree_params,
                    )
                },
            )
            .collect::<Result<Vec<_>, Error>>()?;

        let mut proofs = BoundedVec::with_bounded_capacity(account_assets.len());
        let mut states = Vec::with_capacity(account_assets.len());

        for (proof, state) in proofs_and_states {
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyAccountAssetRegProofs)?;
            states.push(state);
        }

        Ok((Self { proofs }, states))
    }

    /// Generate a new batched account asset registration proof.
    #[cfg(not(feature = "parallel"))]
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account_assets: &[(AccountKeyPair, AssetId, NullifierSkGenCounter)],
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
    ) -> Result<(Self, Vec<AccountAssetState>), Error> {
        let mut proofs = BoundedVec::with_bounded_capacity(account_assets.len());
        let mut states = Vec::with_capacity(account_assets.len());

        for (account, asset_id, counter) in account_assets {
            let (proof, state) = AccountAssetRegistrationProof::new(
                rng,
                account,
                *asset_id,
                *counter,
                identity,
                tree_params,
            )?;
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyAccountAssetRegProofs)?;
            states.push(state);
        }

        Ok((Self { proofs }, states))
    }

    /// Verify the batched account asset registration proof.
    #[cfg(feature = "parallel")]
    pub fn verify<R: RngCore + CryptoRng + Sync + Send + Clone>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        if self.proofs.len() == 0 {
            return Ok(());
        }
        self.proofs
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, proof| proof.verify(identity, tree_params, rng),
            )
            .collect::<Result<(), Error>>()?;
        Ok(())
    }

    /// Verify the batched account asset registration proof.
    #[cfg(not(feature = "parallel"))]
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        for proof in &self.proofs {
            proof.verify(identity, tree_params, rng)?;
        }
        Ok(())
    }

    /// Verify the batched account asset registration proof.
    #[cfg(feature = "parallel")]
    pub fn batched_verify<R: RngCore + CryptoRng + Sync + Send + Clone>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        if self.proofs.len() < 2 {
            return self.verify(identity, tree_params, rng);
        }

        let tuples = self
            .proofs
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, proof| proof.batched_verify(identity, tree_params, rng),
            )
            .collect::<Result<Vec<_>, Error>>()?;

        bulletproofs::r1cs::batch_verify_with_rng(
            tuples,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            rng,
        )?;

        Ok(())
    }

    /// Verify the batched account asset registration proof.
    #[cfg(not(feature = "parallel"))]
    pub fn batched_verify<R: RngCore + CryptoRng + Sync + Send + Clone>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        if self.proofs.len() < 2 {
            return self.verify(identity, tree_params, rng);
        }
        let mut tuples = Vec::with_capacity(self.proofs.len());

        for proof in &self.proofs {
            let tuple = proof.batched_verify(identity, tree_params, rng)?;
            tuples.push(tuple);
        }

        bulletproofs::r1cs::batch_verify_with_rng(
            tuples,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            rng,
        )?;

        Ok(())
    }

    /// Get the number of proofs in the batch.
    pub fn len(&self) -> usize {
        self.proofs.len()
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
            None,
        )?;
        Ok(())
    }

    /// Verify this registration proof inside a batch of proofs.
    pub fn batched_verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<bulletproofs::r1cs::VerificationTuple<PallasA>, Error> {
        let proof = self.proof.decode()?;
        let params = poseidon_params();
        let id = hash_identity::<PallasScalar>(identity);

        Ok(proof.verify_except_bp(
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
            rng,
            None,
        )?)
    }
}

pub(crate) fn try_block_number<T: TryInto<BlockNumber>>(
    block_number: T,
) -> Result<BlockNumber, Error> {
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
        let root = tree_lookup.root()?;
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
            // TODO: Use the caller's identity?
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
        identity: &[u8],
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let id = hash_identity::<PallasScalar>(identity);
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
            id,
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
