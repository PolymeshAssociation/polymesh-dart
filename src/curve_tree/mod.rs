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
    pub x_coord_children: Vec<[CompressedBaseField; L]>,
    pub height: NodeLevel,
}

impl<const L: usize, const M: usize> Default for CompressedCurveTreeRoot<L, M> {
    fn default() -> Self {
        Self {
            commitments: [CompressedAffine::default(); M],
            x_coord_children: vec![[CompressedBaseField::default(); L]; M],
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

    pub fn update<
        P0: SWCurveConfig + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
    >(
        &mut self,
        commitments: &[Affine<P0>; M],
        x_coords: &[P1::BaseField; M],
        child_index: ChildIndex,
    ) -> Result<(), Error> {
        for (tree_index, (com, x_coord)) in commitments.iter().zip(x_coords.iter()).enumerate() {
            self.commitments[tree_index] = CompressedAffine::from(com);
            self.x_coord_children[tree_index][child_index as usize] =
                CompressedBaseField::from_base_field(x_coord)?;
        }
        Ok(())
    }

    pub fn root_node<C: CurveTreeConfig>(&self) -> Result<CurveTreeRoot<L, M, C>, Error> {
        let root = if self.is_even() {
            let mut commitments = [Affine::<C::P0>::zero(); M];
            let mut x_coord_children = Vec::with_capacity(M);
            for ((self_com, self_x_coords), commitment) in self
                .commitments
                .iter()
                .zip(self.x_coord_children.iter())
                .zip(commitments.iter_mut())
            {
                *commitment = self_com.try_into()?;
                let mut x_coords = [C::F0::zero(); L];
                for (self_x_coord, x_coord) in self_x_coords.iter().zip(x_coords.iter_mut()) {
                    *x_coord = self_x_coord.to_base_field()?;
                }
                x_coord_children.push(x_coords);
            }
            Root::Even(RootNode {
                commitments,
                x_coord_children,
            })
        } else {
            let mut commitments = [Affine::<C::P1>::zero(); M];
            let mut x_coord_children = Vec::with_capacity(M);
            for ((self_com, self_x_coords), commitment) in self
                .commitments
                .iter()
                .zip(self.x_coord_children.iter())
                .zip(commitments.iter_mut())
            {
                *commitment = self_com.try_into()?;
                let mut x_coords = [C::F1::zero(); L];
                for (self_x_coord, x_coord) in self_x_coords.iter().zip(x_coords.iter_mut()) {
                    *x_coord = self_x_coord.to_base_field()?;
                }
                x_coord_children.push(x_coords);
            }
            Root::Odd(RootNode {
                commitments,
                x_coord_children,
            })
        };

        Ok(CurveTreeRoot::new(&root)?)
    }
}

/// A lean curve tree that only stores the inner nodes that are necessary to update the tree root.
#[derive(Clone, Encode, Decode, Debug, TypeInfo)]
pub struct LeanCurveTree<const L: usize, const M: usize, C: CurveTreeConfig> {
    even_nodes: BTreeMap<NodePosition, [Affine<C::P0>; M]>,
    odd_nodes: BTreeMap<NodePosition, [Affine<C::P1>; M]>,
    height: NodeLevel,
    next_leaf_index: LeafIndex,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> LeanCurveTree<L, M, C> {
    /// Creates a new instance of `LeanCurveTree` with the given height.
    pub fn new_no_init(height: NodeLevel) -> Self {
        Self {
            even_nodes: BTreeMap::new(),
            odd_nodes: BTreeMap::new(),
            height,
            next_leaf_index: 0,
        }
    }

    /// Creates a new instance of `LeanCurveTree` with the given height.
    pub fn new(
        height: NodeLevel,
        params: &CurveTreeParameters<C>,
        root: &mut CompressedCurveTreeRoot<L, M>,
    ) -> Result<Self, Error> {
        let mut tree = Self::new_no_init(height);
        tree.init(params, root)?;
        Ok(tree)
    }

    fn init(
        &mut self,
        params: &CurveTreeParameters<C>,
        current_root: &mut CompressedCurveTreeRoot<L, M>,
    ) -> Result<(), Error> {
        let height = self.height();
        // Start at the first leaf's location.
        let mut position = NodePosition::leaf(0);
        // Move to the first inner node location above the leaves.
        let (parent_possition, _) = position.parent::<L>();
        position = parent_possition;
        let commitments = [Affine::<C::P1>::zero(); M];
        self.odd_nodes.insert(position, commitments.clone());

        // Store the leaf as the even commitment.
        let mut even_new_child = ChildCommitments::leaf(LeafValue(Affine::<C::P0>::zero()));
        // Use zeroes to initialize the odd commitments.
        let mut odd_new_child = ChildCommitments::inner(commitments);

        // Keep going until we reach the root of the tree.
        while !position.is_root(height) {
            // Move to the parent location and get the child index of the current node.
            let (parent_possition, child_index) = position.parent::<L>();
            position = parent_possition;
            let is_root = position.is_root(height);

            if position.is_even() {
                // If this node does not exist, we need to create it.
                let (commitments, new_x_coords) = init_empty_inner_node::<L, M, C::P1, C::P0>(
                    odd_new_child,
                    &params.odd_parameters.delta,
                    &params.even_parameters,
                )?;
                self.even_nodes.insert(position, commitments.clone());

                // Update the root if needed.
                if is_root {
                    current_root.update::<C::P0, C::P1>(
                        &commitments,
                        &new_x_coords,
                        child_index,
                    )?;
                }

                // Save the new commitment value for updating the parent.
                even_new_child = ChildCommitments::inner(commitments);
            } else {
                // If this node does not exist, we need to create it.
                let (commitments, new_x_coords) = init_empty_inner_node::<L, M, C::P0, C::P1>(
                    even_new_child,
                    &params.even_parameters.delta,
                    &params.odd_parameters,
                )?;
                self.odd_nodes.insert(position, commitments.clone());

                // Update the root if needed.
                if is_root {
                    current_root.update::<C::P1, C::P0>(
                        &commitments,
                        &new_x_coords,
                        child_index,
                    )?;
                }

                // Save the new commitment value for updating the parent.
                odd_new_child = ChildCommitments::inner(commitments);
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
        params: &CurveTreeParameters<C>,
        current_root: &mut CompressedCurveTreeRoot<L, M>,
    ) -> Result<(), Error> {
        let leaf_index = self.next_leaf_index;
        self.next_leaf_index += 1;

        self.update_leaf(new_leaf_value, leaf_index, params, current_root)
    }

    fn update_leaf(
        &mut self,
        new_leaf_value: LeafValue<C::P0>,
        leaf_index: LeafIndex,
        params: &CurveTreeParameters<C>,
        current_root: &mut CompressedCurveTreeRoot<L, M>,
    ) -> Result<(), Error> {
        let height = self.height();
        // Store the leaf as the even commitment.
        let mut even_old_child = None;
        let mut even_new_child = ChildCommitments::leaf(new_leaf_value);
        // Use zeroes to initialize the odd commitments.
        let mut odd_old_child = None;
        let mut odd_new_child = ChildCommitments::leaf(LeafValue(Affine::<C::P1>::zero()));

        // Start at the leaf's location.
        let mut position = NodePosition::leaf(leaf_index);

        // Keep going until we reach the root of the tree.
        while !position.is_root(height) {
            // Move to the parent location and get the child index of the current node.
            let (parent_possition, child_index) = position.parent::<L>();
            position = parent_possition;
            let is_root = position.is_root(height);

            if position.is_even() {
                if let Some(commitments) = self.even_nodes.get_mut(&position) {
                    // We save the old commitment value for updating the parent node.
                    even_old_child = Some(ChildCommitments::inner(*commitments));

                    // Update the node.  We pass both the old and new child commitments.
                    let new_x_coords = update_inner_node::<L, M, C::P1, C::P0>(
                        commitments,
                        child_index,
                        odd_old_child,
                        odd_new_child,
                        &params.odd_parameters.delta,
                        &params.even_parameters,
                    )?;

                    // Update the root if needed.
                    if is_root {
                        current_root.update::<C::P0, C::P1>(
                            commitments,
                            &new_x_coords,
                            child_index,
                        )?;
                    }

                    // Save the new commitment value for updating the parent.
                    even_new_child = ChildCommitments::inner(*commitments);
                } else {
                    // If this node does not exist, we need to create it.
                    let (commitments, new_x_coords) = init_empty_inner_node::<L, M, C::P1, C::P0>(
                        odd_new_child,
                        &params.odd_parameters.delta,
                        &params.even_parameters,
                    )?;
                    self.even_nodes.insert(position, commitments.clone());

                    // Update the root if needed.
                    if is_root {
                        current_root.update::<C::P0, C::P1>(
                            &commitments,
                            &new_x_coords,
                            child_index,
                        )?;
                    }

                    // Save the new commitment value for updating the parent.
                    even_old_child = None;
                    even_new_child = ChildCommitments::inner(commitments);
                }
            } else {
                if let Some(commitments) = self.odd_nodes.get_mut(&position) {
                    // We save the old commitment value for updating the parent node.
                    odd_old_child = Some(ChildCommitments::inner(*commitments));

                    // Update the node.  We pass both the old and new child commitments.
                    let new_x_coords = update_inner_node::<L, M, C::P0, C::P1>(
                        commitments,
                        child_index,
                        even_old_child,
                        even_new_child,
                        &params.even_parameters.delta,
                        &params.odd_parameters,
                    )?;

                    // Update the root if needed.
                    if is_root {
                        current_root.update::<C::P1, C::P0>(
                            commitments,
                            &new_x_coords,
                            child_index,
                        )?;
                    }

                    // Save the new commitment value for updating the parent.
                    odd_new_child = ChildCommitments::inner(*commitments);
                } else {
                    // If this node does not exist, we need to create it.
                    let (commitments, new_x_coords) = init_empty_inner_node::<L, M, C::P0, C::P1>(
                        even_new_child,
                        &params.even_parameters.delta,
                        &params.odd_parameters,
                    )?;
                    self.odd_nodes.insert(position, commitments.clone());

                    // Update the root if needed.
                    if is_root {
                        current_root.update::<C::P1, C::P0>(
                            &commitments,
                            &new_x_coords,
                            child_index,
                        )?;
                    }

                    // Save the new commitment value for updating the parent.
                    odd_old_child = None;
                    odd_new_child = ChildCommitments::inner(commitments);
                }
            }
        }

        // Check if the tree has grown to accommodate the new leaf.
        // if the root's level is higher than the current height, we need to update the height.
        let level = position.level;
        if level > height {
            log::warn!("Tree height increased from {} to {}", height, level);
            self.height = level;
        }
        Ok(())
    }
}
