#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use ark_ec::AffineRepr;
pub use ark_ec::CurveConfig;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::{Zero, vec, vec::Vec};
use blake2::Blake2b512;

pub use curve_tree_relations::{
    curve_tree::{Root, RootNode, SelRerandParameters},
    curve_tree_prover::{CurveTreeWitnessPath, WitnessNode},
    single_level_select_and_rerandomize::SingleLayerParameters,
};

use polymesh_dart_bp::leg as bp_leg;
use polymesh_dart_common::MAX_ASSET_KEYS;

use codec::{Decode, Encode};
use scale_info::TypeInfo;

use super::*;
use crate::curve_tree::{LeafIndex, NodeLevel};
use crate::encode::{CompressedAffine, CompressedBaseField};

pub mod backends;
pub use backends::*;

#[macro_use]
mod common;
pub use common::*;

pub type AssetCommitmentParameters<C> =
    bp_leg::AssetCommitmentParams<<C as CurveTreeConfig>::P1, <C as CurveTreeConfig>::P0>;

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    static ref ASSET_CURVE_TREE_PARAMETERS: CurveTreeParameters<AssetTreeConfig> = AssetTreeConfig::build_parameters();
    static ref ASSET_COMMITMENT_PARAMETERS: AssetCommitmentParameters<AssetTreeConfig> =
        AssetCommitmentParameters::<AssetTreeConfig>::new::<Blake2b512>(
            b"asset-comm-params",
            MAX_ASSET_KEYS,
            &ASSET_CURVE_TREE_PARAMETERS.even_parameters.bp_gens,
        );
    static ref ACCOUNT_CURVE_TREE_PARAMETERS: CurveTreeParameters<AccountTreeConfig> = AccountTreeConfig::build_parameters();
}

#[cfg(not(feature = "std"))]
static mut ASSET_CURVE_TREE_PARAMETERS: Option<CurveTreeParameters<AssetTreeConfig>> = None;
#[cfg(not(feature = "std"))]
static mut ASSET_COMMITMENT_PARAMETERS: Option<AssetCommitmentParameters<AssetTreeConfig>> = None;
#[cfg(not(feature = "std"))]
static mut ACCOUNT_CURVE_TREE_PARAMETERS: Option<CurveTreeParameters<AccountTreeConfig>> = None;

#[cfg(feature = "std")]
pub fn get_asset_curve_tree_parameters() -> &'static CurveTreeParameters<AssetTreeConfig> {
    &ASSET_CURVE_TREE_PARAMETERS
}

#[cfg(feature = "std")]
pub fn get_asset_commitment_parameters() -> &'static AssetCommitmentParameters<AssetTreeConfig> {
    &ASSET_COMMITMENT_PARAMETERS
}

#[cfg(feature = "std")]
pub fn get_account_curve_tree_parameters() -> &'static CurveTreeParameters<AccountTreeConfig> {
    &ACCOUNT_CURVE_TREE_PARAMETERS
}

#[allow(static_mut_refs)]
#[cfg(not(feature = "std"))]
pub fn get_asset_curve_tree_parameters() -> &'static CurveTreeParameters<AssetTreeConfig> {
    unsafe {
        if ASSET_CURVE_TREE_PARAMETERS.is_none() {
            let parameters = AssetTreeConfig::build_parameters();
            ASSET_CURVE_TREE_PARAMETERS = Some(parameters);
        }
        ASSET_CURVE_TREE_PARAMETERS.as_ref().unwrap()
    }
}

#[allow(static_mut_refs)]
#[cfg(not(feature = "std"))]
pub fn get_asset_commitment_parameters() -> &'static AssetCommitmentParameters<AssetTreeConfig> {
    unsafe {
        if ASSET_COMMITMENT_PARAMETERS.is_none() {
            let tree_parameters = get_asset_curve_tree_parameters();
            let parameters = AssetCommitmentParameters::<AssetTreeConfig>::new::<Blake2b512>(
                b"asset-comm-params",
                MAX_ASSET_KEYS,
                &tree_parameters.even_parameters.bp_gens,
            );
            ASSET_COMMITMENT_PARAMETERS = Some(parameters);
        }
        ASSET_COMMITMENT_PARAMETERS.as_ref().unwrap()
    }
}

#[allow(static_mut_refs)]
#[cfg(not(feature = "std"))]
pub fn get_account_curve_tree_parameters() -> &'static CurveTreeParameters<AccountTreeConfig> {
    unsafe {
        if ACCOUNT_CURVE_TREE_PARAMETERS.is_none() {
            let parameters = AccountTreeConfig::build_parameters();
            ACCOUNT_CURVE_TREE_PARAMETERS = Some(parameters);
        }
        ACCOUNT_CURVE_TREE_PARAMETERS.as_ref().unwrap()
    }
}

pub trait CurveTreeConfig:
    Clone + Sized + PartialEq + Eq + core::fmt::Debug + Encode + Decode + TypeInfo + 'static
{
    const L: usize;
    const M: usize;
    const EVEN_GEN_LENGTH: usize;
    const ODD_GEN_LENGTH: usize;
    const APPEND_ONLY: bool;

    type F0: PrimeField + core::fmt::Debug;
    type F1: PrimeField + core::fmt::Debug;
    type P0: SWCurveConfig<ScalarField = Self::F0, BaseField = Self::F1> + Clone + Copy + PartialEq;
    type P1: SWCurveConfig<ScalarField = Self::F1, BaseField = Self::F0> + Clone + Copy + PartialEq;

    fn build_parameters() -> SelRerandParameters<Self::P0, Self::P1> {
        SelRerandParameters::new(Self::EVEN_GEN_LENGTH, Self::ODD_GEN_LENGTH)
            .expect("Failed to create SelRerandParameters")
    }

    fn parameters() -> &'static SelRerandParameters<Self::P0, Self::P1>;
}

#[derive(Debug, Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct AssetTreeConfig;
impl CurveTreeConfig for AssetTreeConfig {
    const L: usize = ASSET_TREE_L;
    const M: usize = ASSET_TREE_M;
    const EVEN_GEN_LENGTH: usize = crate::MAX_CURVE_TREE_GENS;
    const ODD_GEN_LENGTH: usize = crate::MAX_CURVE_TREE_GENS;
    const APPEND_ONLY: bool = false;

    type F0 = <VestaParameters as CurveConfig>::ScalarField;
    type F1 = <PallasParameters as CurveConfig>::ScalarField;
    type P0 = VestaParameters;
    type P1 = PallasParameters;

    fn parameters() -> &'static SelRerandParameters<Self::P0, Self::P1> {
        get_asset_curve_tree_parameters()
    }
}

#[derive(Debug, Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct AccountTreeConfig;
impl CurveTreeConfig for AccountTreeConfig {
    const L: usize = ACCOUNT_TREE_L;
    const M: usize = ACCOUNT_TREE_M;
    const EVEN_GEN_LENGTH: usize = crate::MAX_CURVE_TREE_GENS;
    const ODD_GEN_LENGTH: usize = crate::MAX_CURVE_TREE_GENS;
    const APPEND_ONLY: bool = true;

    type F0 = <PallasParameters as CurveConfig>::ScalarField;
    type F1 = <VestaParameters as CurveConfig>::ScalarField;
    type P0 = PallasParameters;
    type P1 = VestaParameters;

    fn parameters() -> &'static SelRerandParameters<Self::P0, Self::P1> {
        get_account_curve_tree_parameters()
    }
}

#[derive(Debug, Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct WrappedCurveTreeParameters(Vec<u8>);

impl WrappedCurveTreeParameters {
    pub fn new<C: CurveTreeConfig>(gens_length: usize) -> Result<Self, Error> {
        let params = CurveTreeParameters::<C>::new(gens_length, gens_length)?;
        let mut buf = Vec::new();
        params.serialize_uncompressed(&mut buf)?;
        Ok(Self(buf))
    }

    /// Decodes the wrapped value back into its original type `T`.
    pub fn decode<C: CurveTreeConfig>(&self) -> Result<SelRerandParameters<C::P0, C::P1>, Error> {
        Ok(CurveTreeParameters::<C>::deserialize_uncompressed_unchecked(&self.0[..])?)
    }
}

pub type CurveTreeParameters<C> =
    SelRerandParameters<<C as CurveTreeConfig>::P0, <C as CurveTreeConfig>::P1>;
pub type CurveTreePath<const L: usize, C> =
    CurveTreeWitnessPath<L, <C as CurveTreeConfig>::P0, <C as CurveTreeConfig>::P1>;

#[derive(Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(L, M, C))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct CurveTreeRoot<const L: usize, const M: usize, C: CurveTreeConfig>(
    pub WrappedCanonical<Root<L, M, C::P0, C::P1>>,
);

impl<const L: usize, const M: usize, C: CurveTreeConfig> core::fmt::Debug
    for CurveTreeRoot<L, M, C>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("CurveTreeRoot").field(&self.0).finish()
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeRoot<L, M, C> {
    pub fn new(root: &Root<L, M, C::P0, C::P1>) -> Result<Self, Error> {
        Ok(Self(WrappedCanonical::wrap(root)?))
    }

    /// Decodes the wrapped value back into its original type `T`.
    pub fn decode(&self) -> Result<Root<L, M, C::P0, C::P1>, Error> {
        self.0.decode()
    }
}

#[cfg(feature = "async_tree")]
impl_curve_tree_with_backend!(Async, AsyncCurveTreeWithBackend, AsyncCurveTreeBackend);
impl_curve_tree_with_backend!(Sync, CurveTreeWithBackend, CurveTreeBackend);

/// A trait for looking up paths in a curve tree.
pub trait CurveTreeLookup<const L: usize, const M: usize, C: CurveTreeConfig> {
    /// Returns the path to a leaf in the curve tree by its index.
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error>;

    /// Returns the path to a leaf in the curve tree by its value.
    fn get_path_to_leaf(&self, leaf: LeafValue<C::P0>) -> Result<CurveTreePath<L, C>, Error>;

    /// Returns the parameters of the curve tree.
    fn params(&self) -> &CurveTreeParameters<C>;

    /// Returns the root node of the curve tree.
    fn root_node(&self) -> Result<CurveTreeRoot<L, M, C>, Error>;

    /// Returns the block number associated with the current state of the tree.
    fn get_block_number(&self) -> Result<BlockNumber, Error>;
}

/// Check if the tree root is valid.
///
/// This allows verifying proofs against older tree roots.
pub trait ValidateCurveTreeRoot<const L: usize, const M: usize, C: CurveTreeConfig> {
    /// Returns the root of the curve tree for a given block number.
    fn get_block_root(&self, block: BlockNumber) -> Option<CurveTreeRoot<L, M, C>>;

    /// Returns the parameters of the curve tree.
    fn params(&self) -> &CurveTreeParameters<C>;
}

impl<const L: usize, const M: usize> ValidateCurveTreeRoot<L, M, AssetTreeConfig>
    for &CurveTreeRoot<L, M, AssetTreeConfig>
{
    fn get_block_root(&self, _block: BlockNumber) -> Option<CurveTreeRoot<L, M, AssetTreeConfig>> {
        Some((*self).clone())
    }

    fn params(&self) -> &CurveTreeParameters<AssetTreeConfig> {
        get_asset_curve_tree_parameters()
    }
}

impl<const L: usize, const M: usize> ValidateCurveTreeRoot<L, M, AccountTreeConfig>
    for &CurveTreeRoot<L, M, AccountTreeConfig>
{
    fn get_block_root(
        &self,
        _block: BlockNumber,
    ) -> Option<CurveTreeRoot<L, M, AccountTreeConfig>> {
        Some((*self).clone())
    }

    fn params(&self) -> &CurveTreeParameters<AccountTreeConfig> {
        get_account_curve_tree_parameters()
    }
}

pub struct RootHistory<const L: usize, const M: usize, C: CurveTreeConfig> {
    block_roots: BTreeMap<BlockNumber, CurveTreeRoot<L, M, C>>,
    next_block_number: BlockNumber,
    history_length: usize,
    params: CurveTreeParameters<C>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> RootHistory<L, M, C> {
    /// Creates a new instance of `RootHistory` with the given history length and parameters.
    pub fn new(history_length: usize, params: &CurveTreeParameters<C>) -> Self {
        Self {
            block_roots: BTreeMap::new(),
            next_block_number: 0,
            history_length,
            params: params.clone(),
        }
    }

    /// Adds a new root to the history.
    pub fn add_root(&mut self, root: CurveTreeRoot<L, M, C>) -> BlockNumber {
        let block_number = self.next_block_number;
        self.next_block_number += 1;

        if self.block_roots.len() >= self.history_length {
            let to_remove = block_number - self.history_length as BlockNumber;
            self.block_roots.remove(&to_remove);
        }
        self.block_roots.insert(block_number, root);
        block_number
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> ValidateCurveTreeRoot<L, M, C>
    for &RootHistory<L, M, C>
{
    fn get_block_root(&self, block: BlockNumber) -> Option<CurveTreeRoot<L, M, C>> {
        let block: BlockNumber = block.try_into().ok()?;
        self.block_roots.get(&block).cloned()
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        &self.params
    }
}

pub struct FullCurveTree<const L: usize, const M: usize, C: CurveTreeConfig> {
    tree: CurveTreeWithBackend<L, M, C>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> FullCurveTree<L, M, C> {
    /// Creates a new instance of `FullCurveTree` with the given height and generators length.
    pub fn new_with_capacity(height: NodeLevel, gens_length: usize) -> Result<Self, Error> {
        Ok(Self {
            tree: CurveTreeWithBackend::new(height, gens_length)?,
        })
    }

    pub fn height(&self) -> NodeLevel {
        self.tree.height()
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: LeafValue<C::P0>) -> Result<LeafIndex, Error> {
        self.tree.insert_leaf(leaf)
    }

    /// Insert a new leaf into the curve tree without committing it immediately.
    pub fn insert_delayed_update(&mut self, leaf: LeafValue<C::P0>) -> Result<LeafIndex, Error> {
        self.tree.insert_leaf_delayed_update(leaf)
    }

    /// Commits all uncommitted leaves to the curve tree.
    pub fn commit_leaves_to_tree(&mut self) -> Result<bool, Error> {
        self.tree.commit_leaves_to_tree()
    }

    /// Updates an existing leaf in the curve tree.
    pub fn update(&mut self, leaf: LeafValue<C::P0>, leaf_index: LeafIndex) -> Result<(), Error> {
        self.tree.update_leaf(leaf_index, leaf)
    }

    /// Returns the path to a leaf in the curve tree by its index.
    pub fn get_path_to_leaf_index(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<CurveTreePath<L, C>, Error> {
        Ok(self.tree.get_path_to_leaf(leaf_index, 0)?)
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters<C> {
        self.tree.parameters()
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> Result<CurveTreeRoot<L, M, C>, Error> {
        Ok(CurveTreeRoot::<L, M, C>::new(&self.tree.root_node()?)?)
    }

    pub fn set_block_number(&mut self, block_number: BlockNumber) -> Result<(), Error> {
        self.tree.set_block_number(block_number)?;
        Ok(())
    }

    pub fn store_root(&mut self) -> Result<(), Error> {
        self.tree.store_root()?;
        Ok(())
    }

    pub fn fetch_root(&self, block: BlockNumber) -> Result<CurveTreeRoot<L, M, C>, Error> {
        let block = block.into();
        let root = self.tree.fetch_root(block)?;
        Ok(CurveTreeRoot::<L, M, C>::new(&root)?)
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeLookup<L, M, C>
    for &FullCurveTree<L, M, C>
{
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error> {
        Ok(self.tree.get_path_to_leaf(leaf_index, 0)?)
    }

    fn get_path_to_leaf(&self, _leaf: LeafValue<C::P0>) -> Result<CurveTreePath<L, C>, Error> {
        Err(Error::LeafNotFound)
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        self.tree.parameters()
    }

    fn root_node(&self) -> Result<CurveTreeRoot<L, M, C>, Error> {
        Ok(CurveTreeRoot::new(&self.tree.root_node()?)?)
    }

    fn get_block_number(&self) -> Result<BlockNumber, Error> {
        Ok(self.tree.get_block_number()?)
    }
}

/// A Curve Tree for the Verifier in the Dart BP protocol.
///
/// This tree is used to verify the commitments and proofs generated by the Prover.
///
/// It is a lean version of the curve tree, which means it does not store the full tree structure,
pub struct VerifierCurveTree<const L: usize, const M: usize, C: CurveTreeConfig> {
    tree: CurveTreeWithBackend<L, M, C>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> VerifierCurveTree<L, M, C> {
    /// Creates a new instance of `VerifierCurveTree` with the given height and generators length.
    pub fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Error> {
        Ok(Self {
            tree: CurveTreeWithBackend::new(height, gens_length)?,
        })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: LeafValue<C::P0>) -> Result<LeafIndex, Error> {
        self.tree.insert_leaf(leaf.into())
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters<C> {
        self.tree.parameters()
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> Result<CurveTreeRoot<L, M, C>, Error> {
        Ok(CurveTreeRoot::new(&self.tree.root_node()?)?)
    }

    pub fn get_block_number(&self) -> Result<BlockNumber, Error> {
        Ok(self.tree.get_block_number()?)
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

impl<const L: usize, const M: usize, C: CurveTreeConfig> ValidateCurveTreeRoot<L, M, C>
    for &VerifierCurveTree<L, M, C>
{
    fn get_block_root(&self, block: BlockNumber) -> Option<CurveTreeRoot<L, M, C>> {
        self.tree.fetch_root(block).ok().map(|root| {
            CurveTreeRoot::new(&root).expect("Failed to create CurveTreeRoot from block root")
        })
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        self.tree.parameters()
    }
}

/// A Curve Tree for the Prover in the Dart BP protocol.
pub struct ProverCurveTree<
    const L: usize,
    const M: usize,
    C: CurveTreeConfig,
    B: CurveTreeBackend<L, M, C, Error = E> = CurveTreeMemoryBackend<L, M, C>,
    E: From<crate::Error> = crate::Error,
> {
    tree: CurveTreeWithBackend<L, M, C, B, E>,
    leaf_to_index: BTreeMap<Vec<u8>, u64>,
}

impl<
    const L: usize,
    const M: usize,
    C: CurveTreeConfig,
    B: CurveTreeBackend<L, M, C, Error = E>,
    E: From<crate::Error>,
> ProverCurveTree<L, M, C, B, E>
{
    /// Creates a new instance of `ProverCurveTree` with the given height and generators length.
    pub fn new(height: NodeLevel, gens_length: usize) -> Result<Self, E> {
        Ok(Self {
            tree: CurveTreeWithBackend::<L, M, C, B, E>::new_no_init(height, gens_length)?,
            leaf_to_index: BTreeMap::new(),
        })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: LeafValue<C::P0>) -> Result<u64, E> {
        let leaf_index = self.tree.insert_leaf(leaf)? as u64;
        let leaf_buf = leaf.encode();
        self.leaf_to_index.insert(leaf_buf, leaf_index);
        Ok(leaf_index)
    }

    pub fn set_block_number(&mut self, block_number: BlockNumber) -> Result<(), E> {
        self.tree.set_block_number(block_number)?;
        Ok(())
    }

    pub fn store_root(&mut self) -> Result<BlockNumber, E> {
        self.tree.store_root()
    }

    /// Apply updates to the curve tree by inserting multiple untracked leaves.
    pub fn apply_updates(&mut self, leaves: Vec<LeafValue<C::P0>>) -> Result<(), E> {
        for leaf in &leaves {
            self.tree.insert_leaf(*leaf)?;
        }
        Ok(())
    }

    /// Apply new leaves from the backend and insert them into `leaf_to_index` map.
    pub fn apply_new_leaves(&mut self) {
        let mut last_index = self.leaf_to_index.len() as LeafIndex;
        while let Ok(Some(leaf)) = self.tree.get_leaf(last_index) {
            let leaf_buf = leaf.encode();
            self.leaf_to_index.insert(leaf_buf, last_index as u64);
            last_index += 1;
        }
    }

    pub fn params(&self) -> &CurveTreeParameters<C> {
        self.tree.parameters()
    }

    pub fn get_path_and_root(
        &self,
        leaf: LeafValue<C::P0>,
    ) -> Result<LeafPathAndRoot<L, M, C>, Error> {
        let leaf_buf = leaf.encode();
        if let Some(&leaf_index) = self.leaf_to_index.get(&leaf_buf) {
            self.get_path_and_root_by_index(leaf_index)
        } else {
            Err(Error::LeafNotFound)
        }
    }

    pub fn get_path_and_root_by_index(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<LeafPathAndRoot<L, M, C>, Error> {
        Ok(self
            .tree
            .get_path_and_root(leaf_index)
            .map_err(|_| Error::LeafIndexNotFound(leaf_index))?)
    }
}

impl<
    const L: usize,
    const M: usize,
    C: CurveTreeConfig,
    B: CurveTreeBackend<L, M, C, Error = E>,
    E: From<crate::Error>,
> CurveTreeLookup<L, M, C> for &ProverCurveTree<L, M, C, B, E>
{
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error> {
        Ok(self
            .tree
            .get_path_to_leaf(leaf_index, 0)
            .map_err(|_| Error::LeafIndexNotFound(leaf_index))?)
    }

    fn get_path_to_leaf(&self, leaf: LeafValue<C::P0>) -> Result<CurveTreePath<L, C>, Error> {
        let leaf_buf = leaf.encode();
        if let Some(&leaf_index) = self.leaf_to_index.get(&leaf_buf) {
            self.get_path_to_leaf_index(leaf_index)
        } else {
            Err(Error::LeafNotFound)
        }
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        self.tree.parameters()
    }

    fn root_node(&self) -> Result<CurveTreeRoot<L, M, C>, Error> {
        Ok(CurveTreeRoot::new(
            &self
                .tree
                .root_node()
                .map_err(|_| Error::CurveTreeRootNotFound)?,
        )?)
    }

    fn get_block_number(&self) -> Result<BlockNumber, Error> {
        Ok(self
            .tree
            .get_block_number()
            .map_err(|_| Error::CurveTreeBlockNumberNotFound)?)
    }
}

#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct CompressedCurveTreeRoot<const L: usize, const M: usize> {
    pub commitments: [CompressedAffine; M],
    pub x_coord_children: Vec<[CompressedBaseField; M]>,
    pub height: NodeLevel,
}

impl<const L: usize, const M: usize> Default for CompressedCurveTreeRoot<L, M> {
    fn default() -> Self {
        Self {
            commitments: [CompressedAffine::default(); M],
            x_coord_children: vec![[CompressedBaseField::default(); M]; L],
            height: 0,
        }
    }
}

impl<const L: usize, const M: usize> CompressedCurveTreeRoot<L, M> {
    pub fn new<
        P0: SWCurveConfig + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
    >() -> Self {
        let mut root = Self::default();
        let commitments = [Affine::<P0>::zero(); M];
        for (tree_index, com) in commitments.iter().enumerate() {
            root.commitments[tree_index] = CompressedAffine::from(com);
        }
        root
    }

    pub fn is_even(&self) -> bool {
        self.height % 2 == 0
    }

    pub fn compressed_update(
        &mut self,
        commitments: [CompressedAffine; M],
        new_x_coords: [CompressedBaseField; M],
        child_index: ChildIndex,
    ) -> Result<(), Error> {
        // Update the commitments.
        self.commitments = commitments;

        // If `child_index` jumps ahead too far (i.e. isn't the next index), we need to
        // resize the vector to accommodate the new index.
        if child_index > self.x_coord_children.len() as ChildIndex {
            self.x_coord_children.resize(
                (child_index + 1) as usize,
                [CompressedBaseField::default(); M],
            );
        }
        if let Some(old_x_coords) = self.x_coord_children.get_mut(child_index as usize) {
            // Update an existing child's x-coordinates.
            *old_x_coords = new_x_coords;
        } else {
            // Push the new child's x-coordinates.
            self.x_coord_children.push(new_x_coords);
        }
        Ok(())
    }

    pub fn update<
        P0: SWCurveConfig + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
    >(
        &mut self,
        new_commitments: &[Affine<P0>; M],
        new_x_coords: &[P1::BaseField; M],
        child_index: ChildIndex,
    ) -> Result<(), Error> {
        let mut commitments = [CompressedAffine::default(); M];
        for (tree_index, com) in new_commitments.iter().enumerate() {
            commitments[tree_index] = CompressedAffine::from(com);
        }
        let mut x_coords = [CompressedBaseField::default(); M];
        for (tree_index, new_x_coord) in new_x_coords.iter().enumerate() {
            x_coords[tree_index] = CompressedBaseField::from_base_field(new_x_coord)?;
        }
        self.compressed_update(commitments, x_coords, child_index)
    }

    fn decompress<
        P0: SWCurveConfig + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
    >(
        &self,
    ) -> Result<RootNode<L, M, P0, P1>, Error> {
        let mut commitments = [Affine::<P0>::zero(); M];
        for (self_com, commitment) in self.commitments.iter().zip(commitments.iter_mut()) {
            *commitment = self_com.try_into()?;
        }
        let mut x_coord_children = Vec::with_capacity(M);
        for tree_index in 0..M {
            let mut x_coords = [<P1 as CurveConfig>::BaseField::zero(); L];
            for (self_x_coord, x_coord) in self.x_coord_children.iter().zip(x_coords.iter_mut()) {
                *x_coord = self_x_coord[tree_index].to_base_field()?;
            }
            x_coord_children.push(x_coords);
        }
        Ok(RootNode {
            commitments,
            x_coord_children,
        })
    }

    pub fn root_node<C: CurveTreeConfig>(&self) -> Result<CurveTreeRoot<L, M, C>, Error> {
        let root = if self.is_even() {
            Root::Even(self.decompress::<C::P0, C::P1>()?)
        } else {
            Root::Odd(self.decompress::<C::P1, C::P0>()?)
        };

        Ok(CurveTreeRoot::new(&root)?)
    }
}

/// A lean curve tree that only stores the inner nodes that are necessary to update the tree root.
#[derive(Clone, Encode, Decode, Debug, TypeInfo)]
pub struct LeanCurveTree<
    const L: usize,
    const M: usize,
    C: CurveTreeConfig,
    U: CurveTreeUpdater<L, M, C> = DefaultCurveTreeUpdater<L, M, C>,
> {
    nodes: BTreeMap<NodeLocation<L>, Inner<M, C>>,
    height: NodeLevel,
    next_leaf_index: LeafIndex,
    _updater: core::marker::PhantomData<U>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig, U: CurveTreeUpdater<L, M, C>>
    LeanCurveTree<L, M, C, U>
{
    /// Creates a new instance of `LeanCurveTree` with the given height.
    pub fn new_no_init(height: NodeLevel) -> Self {
        Self {
            nodes: BTreeMap::new(),
            height,
            next_leaf_index: 0,
            _updater: core::marker::PhantomData,
        }
    }

    /// Creates a new instance of `LeanCurveTree` with the given height.
    pub fn new(height: NodeLevel, root: &mut CompressedCurveTreeRoot<L, M>) -> Result<Self, Error> {
        let mut tree = Self::new_no_init(height);
        tree.init(root)?;
        Ok(tree)
    }

    fn init(&mut self, current_root: &mut CompressedCurveTreeRoot<L, M>) -> Result<(), Error> {
        let height = self.height();
        // Start at the first leaf's location.
        let mut location = NodeLocation::leaf(0);
        // Move to the first inner node location above the leaves.
        let (parent_possition, _) = location.parent();
        location = parent_possition;
        let mut is_root = location.is_root(height);
        let commitments = [Affine::<C::P1>::zero(); M];
        self.nodes.insert(location, Inner::Odd(commitments));

        let mut updater = U::new();

        // Keep going until we reach the root of the tree.
        while !is_root {
            // Move to the parent location and get the child index of the current node.
            let (parent_possition, child_index) = location.parent();
            location = parent_possition;
            is_root = location.is_root(height);

            if location.is_even() {
                let mut commitments = [Affine::<C::P0>::zero(); M];
                updater.update_even_node(
                    &mut commitments,
                    child_index,
                    None,
                    if is_root { Some(current_root) } else { None },
                )?;
                self.nodes.insert(location, Inner::Even(commitments));
            } else {
                let mut commitments = [Affine::<C::P1>::zero(); M];
                updater.update_odd_node(
                    &mut commitments,
                    child_index,
                    None,
                    if is_root { Some(current_root) } else { None },
                )?;
                self.nodes.insert(location, Inner::Odd(commitments));
            }
        }

        Ok(())
    }

    /// Returns the height of the curve tree.
    pub fn height(&self) -> NodeLevel {
        self.height
    }

    pub fn append_leaf(
        &mut self,
        new_leaf_value: LeafValue<C::P0>,
        current_root: &mut CompressedCurveTreeRoot<L, M>,
    ) -> Result<(), Error> {
        self.batch_append_leaves(&[new_leaf_value], current_root, None)
    }

    pub fn batch_append_leaves(
        &mut self,
        leaves: &[LeafValue<C::P0>],
        current_root: &mut CompressedCurveTreeRoot<L, M>,
        mut updated_nodes: Option<&mut BTreeMap<NodeLocation<L>, Inner<M, C>>>,
    ) -> Result<(), Error> {
        let leaf_index_base = self.next_leaf_index;
        let mut leaf_idx = 0;
        let leaf_count = leaves.len() as LeafIndex;
        self.next_leaf_index += leaf_count;

        let mut updater = U::new();

        while leaf_idx < leaf_count {
            let leaf_value = leaves[leaf_idx as usize];

            updater.next_leaf(None, leaf_value);

            // Start at the leaf's location.
            let mut location = NodeLocation::<L>::leaf(leaf_index_base + leaf_idx);
            let mut is_root = location.is_root(self.height);
            let mut child_is_leaf = true;

            leaf_idx += 1;
            // Keep going until we reach the root of the tree.
            while !is_root {
                // Move to the parent location and get the child index of the current node.
                let (parent_location, mut child_index) = location.parent();
                location = parent_location;
                is_root = location.is_root(self.height);

                // Get or initialize the node at this location.
                let mut is_new_node = false;
                let node = self.nodes.entry(location).or_insert_with(|| {
                    is_new_node = true;
                    if location.is_even() {
                        // Create a new even node with zero commitments.
                        Inner::Even([Affine::<C::P0>::zero(); M])
                    } else {
                        // Create a new odd node with zero commitments.
                        Inner::Odd([Affine::<C::P1>::zero(); M])
                    }
                });

                match node {
                    Inner::Even(commitments) => {
                        updater.update_even_node(
                            commitments,
                            child_index,
                            Some(is_new_node),
                            if is_root { Some(current_root) } else { None },
                        )?;
                    }
                    Inner::Odd(commitments) => {
                        updater.update_odd_node(
                            commitments,
                            child_index,
                            Some(is_new_node),
                            if is_root { Some(current_root) } else { None },
                        )?;

                        // If the child was a leaf, we may need to commit multiple leaves to this node.
                        if child_is_leaf {
                            // Try to commit as many leaves as possible to this node.
                            while child_index < L as ChildIndex - 1 && leaf_idx < leaf_count {
                                // Commit the next child leaf.
                                child_index += 1;
                                // Get the next uncommitted leaf.
                                let leaf_value = leaves[leaf_idx as usize];
                                updater.next_leaf(None, leaf_value);
                                leaf_idx += 1;

                                updater.update_odd_node(
                                    commitments,
                                    child_index,
                                    None,
                                    if is_root { Some(current_root) } else { None },
                                )?;
                            }
                        }

                        // Save the new commitment value for updating the parent.
                        child_is_leaf = false;
                    }
                }

                // If we are tracking updated nodes, store the updated node.
                if let Some(updated_nodes) = &mut updated_nodes {
                    updated_nodes.insert(location, node.clone());
                }

                // If we created a new node, we can remove its left sibling if it exists.
                if is_new_node {
                    if let Some(left_sibling) = location.left_sibling() {
                        self.nodes.remove(&left_sibling);
                    }
                }
            }

            // Check if the tree has grown to accommodate the new leaf.
            // if the root's level is higher than the current height, we need to update the height.
            let level = location.level();
            if level > self.height {
                log::warn!("Tree height increased from {} to {}", self.height, level);
                self.height = level;
            }
        }

        Ok(())
    }
}

/// Curve Tree updater trait.
///
/// This allows using different implementations of the update logic (e.g. using native host functions in Substrate runtimes).
pub trait CurveTreeUpdater<const L: usize, const M: usize, C: CurveTreeConfig> {
    fn new() -> Self;

    fn next_leaf(&mut self, old_leaf: Option<LeafValue<C::P0>>, new_leaf: LeafValue<C::P0>);

    fn update_even_node(
        &mut self,
        commitments: &mut [Affine<C::P0>; M],
        child_index: ChildIndex,
        update_old: Option<bool>,
        current_root: Option<&mut CompressedCurveTreeRoot<L, M>>,
    ) -> Result<(), Error>;

    fn update_odd_node(
        &mut self,
        commitments: &mut [Affine<C::P1>; M],
        child_index: ChildIndex,
        update_old: Option<bool>,
        current_root: Option<&mut CompressedCurveTreeRoot<L, M>>,
    ) -> Result<(), Error>;
}

/// Curve tree updater that helps updating the tree root when a leaf is added or updated.
#[derive(Clone, Encode, Decode)]
pub struct DefaultCurveTreeUpdater<const L: usize, const M: usize, C: CurveTreeConfig> {
    even_old_child: Option<ChildCommitments<M, C::P0>>,
    even_new_child: ChildCommitments<M, C::P0>,
    odd_old_child: Option<ChildCommitments<M, C::P1>>,
    odd_new_child: ChildCommitments<M, C::P1>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeUpdater<L, M, C>
    for DefaultCurveTreeUpdater<L, M, C>
{
    fn new() -> Self {
        Self {
            even_old_child: None,
            even_new_child: ChildCommitments::leaf(LeafValue(Affine::<C::P0>::zero())),
            odd_old_child: None,
            odd_new_child: ChildCommitments::leaf(LeafValue(Affine::<C::P1>::zero())),
        }
    }

    fn next_leaf(&mut self, old_leaf: Option<LeafValue<C::P0>>, new_leaf: LeafValue<C::P0>) {
        self.even_old_child = old_leaf.map(ChildCommitments::leaf);
        self.even_new_child = ChildCommitments::leaf(new_leaf);
    }

    fn update_even_node(
        &mut self,
        commitments: &mut [Affine<C::P0>; M],
        child_index: ChildIndex,
        update_old: Option<bool>,
        current_root: Option<&mut CompressedCurveTreeRoot<L, M>>,
    ) -> Result<(), Error> {
        let params = C::parameters();

        if let Some(is_new_node) = update_old {
            if is_new_node {
                // We save the old commitment value for updating the parent node.
                self.even_old_child = None;
            } else {
                // We save the old commitment value for updating the parent node.
                self.even_old_child = Some(ChildCommitments::inner(*commitments));
            }
        }

        // Update the node.  We pass both the old and new child commitments.
        let new_x_coords = update_inner_node::<L, M, C::P1, C::P0>(
            commitments,
            child_index,
            self.odd_old_child,
            self.odd_new_child,
            &params.odd_parameters.delta,
            &params.even_parameters,
        )?;

        // Update the root if needed.
        if let Some(current_root) = current_root {
            current_root.update::<C::P0, C::P1>(commitments, &new_x_coords, child_index)?;
        }

        // Save the new commitment value for updating the parent.
        self.even_new_child = ChildCommitments::inner(*commitments);

        Ok(())
    }

    fn update_odd_node(
        &mut self,
        commitments: &mut [Affine<C::P1>; M],
        child_index: ChildIndex,
        update_old: Option<bool>,
        current_root: Option<&mut CompressedCurveTreeRoot<L, M>>,
    ) -> Result<(), Error> {
        let params = C::parameters();

        if let Some(is_new_node) = update_old {
            if is_new_node {
                // We save the old commitment value for updating the parent node.
                self.odd_old_child = None;
            } else {
                // We save the old commitment value for updating the parent node.
                self.odd_old_child = Some(ChildCommitments::inner(*commitments));
            }
        }

        // Update the node.  We pass both the old and new child commitments.
        let new_x_coords = update_inner_node::<L, M, C::P0, C::P1>(
            commitments,
            child_index,
            self.even_old_child,
            self.even_new_child,
            &params.even_parameters.delta,
            &params.odd_parameters,
        )?;

        // Update the root if needed.
        if let Some(current_root) = current_root {
            current_root.update::<C::P1, C::P0>(commitments, &new_x_coords, child_index)?;
        }

        // Save the new commitment value for updating the parent.
        self.odd_new_child = ChildCommitments::inner(*commitments);

        Ok(())
    }
}
