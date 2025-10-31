use core::marker::PhantomData;

use ark_ec::AffineRepr;
pub use ark_ec::CurveConfig;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::{Zero, vec, vec::Vec};

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

const CURVE_TREE_PARAMETERS_PALLAS_LABEL: &[u8] = b"curve-tree-pallas";
const CURVE_TREE_PARAMETERS_VESTA_LABEL: &[u8] = b"curve-tree-vesta";
const ASSET_COMMITMENT_PARAMETERS_LABEL: &[u8] = b"asset-comm-params";

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    static ref CURVE_TREE_PARAMETERS_PALLAS: SingleLayerParameters<PallasParameters> = SingleLayerParameters::<PallasParameters>::new_using_label(CURVE_TREE_PARAMETERS_PALLAS_LABEL, MAX_CURVE_TREE_GENS as u32).expect("Failed to create SingleLayerParameters for Pallas");
    static ref CURVE_TREE_PARAMETERS_VESTA: SingleLayerParameters<VestaParameters> = SingleLayerParameters::<VestaParameters>::new_using_label(CURVE_TREE_PARAMETERS_VESTA_LABEL, MAX_CURVE_TREE_GENS as u32).expect("Failed to create SingleLayerParameters for Vesta");
    static ref ASSET_CURVE_TREE_PARAMETERS: CurveTreeParameters<AssetTreeConfig> = AssetTreeConfig::build_parameters();
    static ref ASSET_COMMITMENT_PARAMETERS: AssetCommitmentParameters<AssetTreeConfig> =
        AssetCommitmentParameters::<AssetTreeConfig>::new(
            ASSET_COMMITMENT_PARAMETERS_LABEL,
            MAX_ASSET_KEYS as u32,
            &ASSET_CURVE_TREE_PARAMETERS.even_parameters.bp_gens,
        );
    static ref ACCOUNT_CURVE_TREE_PARAMETERS: CurveTreeParameters<AccountTreeConfig> = AccountTreeConfig::build_parameters();
}

#[cfg(not(feature = "std"))]
static mut CURVE_TREE_PARAMETERS_PALLAS: Option<SingleLayerParameters<PallasParameters>> = None;
#[cfg(not(feature = "std"))]
static mut CURVE_TREE_PARAMETERS_VESTA: Option<SingleLayerParameters<VestaParameters>> = None;
#[cfg(not(feature = "std"))]
static mut ASSET_CURVE_TREE_PARAMETERS: Option<CurveTreeParameters<AssetTreeConfig>> = None;
#[cfg(not(feature = "std"))]
static mut ASSET_COMMITMENT_PARAMETERS: Option<AssetCommitmentParameters<AssetTreeConfig>> = None;
#[cfg(not(feature = "std"))]
static mut ACCOUNT_CURVE_TREE_PARAMETERS: Option<CurveTreeParameters<AccountTreeConfig>> = None;

#[cfg(feature = "std")]
pub fn get_pallas_layer_parameters() -> &'static SingleLayerParameters<PallasParameters> {
    &CURVE_TREE_PARAMETERS_PALLAS
}

#[cfg(feature = "std")]
pub fn get_vesta_layer_parameters() -> &'static SingleLayerParameters<VestaParameters> {
    &CURVE_TREE_PARAMETERS_VESTA
}

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
pub fn get_pallas_layer_parameters() -> &'static SingleLayerParameters<PallasParameters> {
    unsafe {
        if CURVE_TREE_PARAMETERS_PALLAS.is_none() {
            let parameters = SingleLayerParameters::<PallasParameters>::new_using_label(
                CURVE_TREE_PARAMETERS_PALLAS_LABEL,
                MAX_CURVE_TREE_GENS as u32,
            )
            .expect("Failed to create SingleLayerParameters for Pallas");
            CURVE_TREE_PARAMETERS_PALLAS = Some(parameters);
        }
        CURVE_TREE_PARAMETERS_PALLAS.as_ref().unwrap()
    }
}

#[allow(static_mut_refs)]
#[cfg(not(feature = "std"))]
pub fn get_vesta_layer_parameters() -> &'static SingleLayerParameters<VestaParameters> {
    unsafe {
        if CURVE_TREE_PARAMETERS_VESTA.is_none() {
            let parameters = SingleLayerParameters::<VestaParameters>::new_using_label(
                CURVE_TREE_PARAMETERS_VESTA_LABEL,
                MAX_CURVE_TREE_GENS as u32,
            )
            .expect("Failed to create SingleLayerParameters for Vesta");
            CURVE_TREE_PARAMETERS_VESTA = Some(parameters);
        }
        CURVE_TREE_PARAMETERS_VESTA.as_ref().unwrap()
    }
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
            let parameters = AssetCommitmentParameters::<AssetTreeConfig>::new(
                ASSET_COMMITMENT_PARAMETERS_LABEL,
                MAX_ASSET_KEYS as u32,
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
    Clone
    + Copy
    + Sized
    + PartialEq
    + Eq
    + core::fmt::Debug
    + Encode
    + Decode
    + TypeInfo
    + Send
    + Sync
    + 'static
{
    const L: usize;
    const M: usize;
    const EVEN_GEN_LENGTH: usize;
    const ODD_GEN_LENGTH: usize;
    const APPEND_ONLY: bool;

    type F0: PrimeField + core::fmt::Debug;
    type F1: PrimeField + core::fmt::Debug;
    type P0: SWCurveConfig<ScalarField = Self::F0, BaseField = Self::F1>
        + Clone
        + Copy
        + PartialEq
        + Eq;
    type P1: SWCurveConfig<ScalarField = Self::F1, BaseField = Self::F0>
        + Clone
        + Copy
        + PartialEq
        + Eq;

    fn build_parameters() -> SelRerandParameters<Self::P0, Self::P1>;

    fn parameters() -> &'static SelRerandParameters<Self::P0, Self::P1>;
}

// NOTE: Currently build_parameters uses unsafe but its also called from unsafe code except in tests or
// the in-memory backend so nowhere serious. This approach will soon be phased out anyway.

#[derive(Debug, Clone, Copy, Encode, Decode, TypeInfo, PartialEq, Eq)]
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

    fn build_parameters() -> SelRerandParameters<Self::P0, Self::P1> {
        SelRerandParameters {
            even_parameters: get_vesta_layer_parameters().clone(),
            odd_parameters: get_pallas_layer_parameters().clone(),
        }
    }

    fn parameters() -> &'static SelRerandParameters<Self::P0, Self::P1> {
        get_asset_curve_tree_parameters()
    }
}

#[derive(Debug, Clone, Copy, Encode, Decode, TypeInfo, PartialEq, Eq)]
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

    fn build_parameters() -> SelRerandParameters<Self::P0, Self::P1> {
        SelRerandParameters {
            odd_parameters: get_vesta_layer_parameters().clone(),
            even_parameters: get_pallas_layer_parameters().clone(),
        }
    }

    fn parameters() -> &'static SelRerandParameters<Self::P0, Self::P1> {
        get_account_curve_tree_parameters()
    }
}

#[derive(Debug, Clone, Copy, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct FeeAccountTreeConfig;
impl CurveTreeConfig for FeeAccountTreeConfig {
    const L: usize = FEE_ACCOUNT_TREE_L;
    const M: usize = FEE_ACCOUNT_TREE_M;
    const EVEN_GEN_LENGTH: usize = crate::MAX_CURVE_TREE_GENS;
    const ODD_GEN_LENGTH: usize = crate::MAX_CURVE_TREE_GENS;
    const APPEND_ONLY: bool = true;

    type F0 = <PallasParameters as CurveConfig>::ScalarField;
    type F1 = <VestaParameters as CurveConfig>::ScalarField;
    type P0 = PallasParameters;
    type P1 = VestaParameters;

    fn build_parameters() -> SelRerandParameters<Self::P0, Self::P1> {
        SelRerandParameters {
            odd_parameters: get_vesta_layer_parameters().clone(),
            even_parameters: get_pallas_layer_parameters().clone(),
        }
    }

    fn parameters() -> &'static SelRerandParameters<Self::P0, Self::P1> {
        get_account_curve_tree_parameters()
    }
}

#[derive(Debug, Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct WrappedCurveTreeParameters(Vec<u8>);

impl WrappedCurveTreeParameters {
    pub fn new<C: CurveTreeConfig>() -> Result<Self, Error> {
        let params = C::build_parameters();
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

#[cfg(feature = "async_tree")]
impl_curve_tree_with_backend!(Async, AsyncCurveTreeWithBackend, AsyncCurveTreeBackend);
impl_curve_tree_with_backend!(Sync, CurveTreeWithBackend, CurveTreeBackend);

/// A trait for looking up paths in a curve tree.
pub trait CurveTreeLookup<const L: usize, const M: usize, C: CurveTreeConfig> {
    /// Returns the path to a leaf in the curve tree by its index.
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error>;

    /// Returns the path to a leaf in the curve tree by its value.
    fn get_path_to_leaf(&self, leaf: CompressedLeafValue<C>) -> Result<CurveTreePath<L, C>, Error>;

    /// Returns the parameters of the curve tree.
    fn params(&self) -> &CurveTreeParameters<C>;

    /// Returns the root of the curve tree.
    fn root(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, Error>;

    /// Returns the block number associated with the current state of the tree.
    fn get_block_number(&self) -> Result<BlockNumber, Error>;
}

// Implement CurveTreeLookup for references to types that implement CurveTreeLookup.
impl<const L: usize, const M: usize, C: CurveTreeConfig, T: CurveTreeLookup<L, M, C>>
    CurveTreeLookup<L, M, C> for &T
{
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error> {
        (*self).get_path_to_leaf_index(leaf_index)
    }

    fn get_path_to_leaf(&self, leaf: CompressedLeafValue<C>) -> Result<CurveTreePath<L, C>, Error> {
        (*self).get_path_to_leaf(leaf)
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        (*self).params()
    }

    fn root(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
        (*self).root()
    }

    fn get_block_number(&self) -> Result<BlockNumber, Error> {
        (*self).get_block_number()
    }
}

/// Check if the tree root is valid.
///
/// This allows verifying proofs against older tree roots.
pub trait ValidateCurveTreeRoot<const L: usize, const M: usize, C: CurveTreeConfig> {
    /// Returns the root of the curve tree for a given block number.
    fn get_block_root(&self, block: BlockNumber) -> Option<CompressedCurveTreeRoot<L, M, C>>;

    /// Returns the parameters of the curve tree.
    fn params(&self) -> &CurveTreeParameters<C>;
}

/// Implement ValidateCurveTreeRoot for references to types that implement ValidateCurveTreeRoot.
impl<const L: usize, const M: usize, C: CurveTreeConfig, T: ValidateCurveTreeRoot<L, M, C>>
    ValidateCurveTreeRoot<L, M, C> for &T
{
    fn get_block_root(&self, block: BlockNumber) -> Option<CompressedCurveTreeRoot<L, M, C>> {
        (*self).get_block_root(block)
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        C::parameters()
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> ValidateCurveTreeRoot<L, M, C>
    for CompressedCurveTreeRoot<L, M, C>
{
    fn get_block_root(&self, _block: BlockNumber) -> Option<CompressedCurveTreeRoot<L, M, C>> {
        Some((*self).clone())
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        C::parameters()
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
    /// Creates a new instance of `ProverCurveTree`.
    pub fn new(height: NodeLevel) -> Result<Self, E> {
        Ok(Self {
            tree: CurveTreeWithBackend::<L, M, C, B, E>::new(height)?,
            leaf_to_index: BTreeMap::new(),
        })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: CompressedLeafValue<C>) -> Result<u64, E> {
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

    pub fn root(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, E> {
        self.tree.root()
    }

    /// Apply updates to the curve tree by inserting multiple untracked leaves.
    pub fn apply_updates(&mut self, leaves: Vec<CompressedLeafValue<C>>) -> Result<(), E> {
        for leaf in leaves {
            self.tree.insert_leaf(leaf)?;
        }
        Ok(())
    }

    /// Apply new leaves from the backend and insert them into `leaf_to_index` map.
    pub fn apply_new_leaves(&mut self) {
        let mut last_index = self.leaf_to_index.len() as LeafIndex;
        while let Ok(Some(leaf)) = self.tree.get_leaf(last_index, None) {
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
        leaf: CompressedLeafValue<C>,
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
> CurveTreeLookup<L, M, C> for ProverCurveTree<L, M, C, B, E>
{
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error> {
        Ok(self
            .tree
            .get_path_to_leaf(leaf_index, 0, None)
            .map_err(|_| Error::LeafIndexNotFound(leaf_index))?)
    }

    fn get_path_to_leaf(&self, leaf: CompressedLeafValue<C>) -> Result<CurveTreePath<L, C>, Error> {
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

    fn root(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
        self.tree.root().map_err(|_| Error::CurveTreeRootNotFound)
    }

    fn get_block_number(&self) -> Result<BlockNumber, Error> {
        Ok(self
            .tree
            .get_block_number()
            .map_err(|_| Error::CurveTreeBlockNumberNotFound)?)
    }
}

/// Represents a tree of asset states in the Dart BP protocol.
pub struct AssetCurveTree {
    pub tree: CurveTreeWithBackend<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>,
    assets: BTreeMap<AssetId, (LeafIndex, AssetState)>,
}

impl AssetCurveTree {
    /// Creates a new instance of `AssetCurveTree` with the specified parameters.
    pub fn new() -> Result<Self, Error> {
        Ok(Self {
            tree: CurveTreeWithBackend::new(ASSET_TREE_HEIGHT)?,
            assets: BTreeMap::new(),
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
        use ark_std::collections::btree_map::Entry;
        match self.assets.entry(asset_id) {
            Entry::Occupied(mut entry) => {
                let (index, existing_state) = entry.get_mut();
                *existing_state = state;
                let index = *index;
                // Update the leaf in the curve tree.
                self.tree.update_leaf(index, leaf)?;

                Ok(index)
            }
            Entry::Vacant(entry) => {
                let index = self.tree.insert_leaf(leaf)?;
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
        self.tree.get_path_to_leaf(*leaf_index, 0, None).ok()
    }

    pub fn params(&self) -> &CurveTreeParameters<AssetTreeConfig> {
        self.tree.parameters()
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

impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig> for &AssetCurveTree {
    fn get_block_root(
        &self,
        block_number: BlockNumber,
    ) -> Option<CompressedCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>> {
        self.tree.fetch_root(Some(block_number)).ok()
    }

    fn params(&self) -> &CurveTreeParameters<AssetTreeConfig> {
        self.tree.parameters()
    }
}

#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct CompressedCurveTreeRoot<const L: usize, const M: usize, C: CurveTreeConfig> {
    pub commitments: [CompressedAffine; M],
    pub x_coord_children: Vec<[CompressedBaseField; M]>,
    pub height: NodeLevel,
    _marker: PhantomData<C>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> Default
    for CompressedCurveTreeRoot<L, M, C>
{
    fn default() -> Self {
        Self {
            commitments: [CompressedAffine::zero::<C::P1>(); M],
            x_coord_children: vec![],
            height: 1,
            _marker: PhantomData,
        }
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CompressedCurveTreeRoot<L, M, C> {
    pub fn new(height: NodeLevel) -> Self {
        let commitments = if height % 2 == 0 {
            [CompressedAffine::zero::<C::P0>(); M]
        } else {
            [CompressedAffine::zero::<C::P1>(); M]
        };
        Self {
            commitments,
            x_coord_children: vec![],
            height,
            _marker: PhantomData,
        }
    }

    pub fn from_root_node(
        height: NodeLevel,
        root: Root<L, M, C::P0, C::P1>,
    ) -> Result<Self, Error> {
        let mut compressed = match root {
            Root::Even(r) => Self::compress::<C::P0, C::P1>(&r)?,
            Root::Odd(r) => Self::compress::<C::P1, C::P0>(&r)?,
        };
        compressed.height = height;
        Ok(compressed)
    }

    pub fn compress<
        P0: SWCurveConfig + Copy + Send,
        P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
    >(
        root: &RootNode<L, M, P0, P1>,
    ) -> Result<Self, Error> {
        let mut commitments = [CompressedAffine::default(); M];
        for (tree_index, com) in root.commitments.iter().enumerate() {
            commitments[tree_index] = CompressedAffine::from(com);
        }
        let mut x_coord_children = Vec::with_capacity(L);
        let mut last_non_zero_child = -1;
        for child_index in 0..L {
            let mut x_coords = [CompressedBaseField::default(); M];
            let mut is_zero = true;
            for tree_index in 0..M {
                let x_coord = root.x_coord_children[tree_index][child_index];
                if x_coord != P1::BaseField::zero() {
                    is_zero = false;
                    x_coords[tree_index] = CompressedBaseField::from_base_field(&x_coord)?;
                }
            }
            if !is_zero {
                last_non_zero_child = child_index as isize;
            }
            x_coord_children.push(x_coords);
        }
        // Trim the trailing zero children to save space.
        if last_non_zero_child < L as isize {
            x_coord_children.truncate((last_non_zero_child + 1) as usize);
        }
        Ok(Self {
            commitments,
            x_coord_children,
            height: 0,
            _marker: PhantomData,
        })
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
            for (child_index, self_x_coord) in self.x_coord_children.iter().enumerate() {
                x_coords[child_index] = self_x_coord[tree_index].to_base_field()?;
            }
            x_coord_children.push(x_coords);
        }
        Ok(RootNode {
            commitments,
            x_coord_children,
        })
    }

    pub fn root_node(&self) -> Result<Root<L, M, C::P0, C::P1>, Error> {
        Ok(if self.is_even() {
            Root::Even(self.decompress::<C::P0, C::P1>()?)
        } else {
            Root::Odd(self.decompress::<C::P1, C::P0>()?)
        })
    }

    pub fn is_even(&self) -> bool {
        self.height % 2 == 0
    }

    pub fn height(&self) -> NodeLevel {
        self.height
    }

    pub fn increase_height<U: CurveTreeUpdater<L, M, C>>(&mut self) -> Result<(), Error> {
        self.height += 1;

        if self.is_even() {
            // The new root node is Even.
            let mut inner = CompressedInner::default_even();
            // The old root is the first child of the new root node.
            let odd_new_child = CompressedChildCommitments::Inner(self.commitments);

            let new_x_coords = U::update_node(&mut inner, 0, None, odd_new_child)?.x_coords;

            // Save the new root commitments and child x-coordinates.
            self.commitments = inner.commitments;
            self.x_coord_children = vec![new_x_coords];
        } else {
            // The new root node is Odd.
            let mut inner = CompressedInner::default_odd();
            // The old root is the first child of the new root node.
            let odd_new_child = CompressedChildCommitments::Inner(self.commitments);

            let new_x_coords = U::update_node(&mut inner, 0, None, odd_new_child)?.x_coords;

            // Save the new root commitments and child x-coordinates.
            self.commitments = inner.commitments;
            self.x_coord_children = vec![new_x_coords];
        }

        Ok(())
    }

    pub fn compressed_update(
        &mut self,
        commitments: [CompressedAffine; M],
        new_x_coords: CompressedXCoords<M>,
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
            *old_x_coords = new_x_coords.x_coords;
        } else {
            // Push the new child's x-coordinates.
            self.x_coord_children.push(new_x_coords.x_coords);
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
        let x_coords = CompressedXCoords::compress::<P1>(new_x_coords)?;
        self.compressed_update(commitments, x_coords, child_index)
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
    nodes: BTreeMap<NodeLocation<L>, CompressedInner<M, C>>,
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
    pub fn new(
        height: NodeLevel,
        root: &mut CompressedCurveTreeRoot<L, M, C>,
    ) -> Result<Self, Error> {
        let mut tree = Self::new_no_init(height);
        tree.init(root)?;
        Ok(tree)
    }

    fn init(&mut self, current_root: &mut CompressedCurveTreeRoot<L, M, C>) -> Result<(), Error> {
        let height = self.height();

        let mut even_new_child = CompressedChildCommitments::zero::<C::P0>();
        let mut odd_new_child = CompressedChildCommitments::zero::<C::P1>();

        // Start at the first leaf's location.
        let mut location = NodeLocation::leaf(0);

        // Move to the first inner node location above the leaves.
        let (parent_possition, _) = location.parent();
        location = parent_possition;

        let mut is_root = location.is_root(height);
        let inner = CompressedInner::default_odd();
        // Update the root
        if is_root {
            current_root.compressed_update(inner.commitments, CompressedXCoords::default(), 0)?;
        }
        self.nodes.insert(location, inner);

        // Keep going until we reach the root of the tree.
        while !is_root {
            // Move to the parent location and get the child index of the current node.
            let (parent_possition, child_index) = location.parent();
            location = parent_possition;
            is_root = location.is_root(height);

            if location.is_even() {
                let mut inner = CompressedInner::default_even();
                let new_x_coords = U::update_node(&mut inner, child_index, None, odd_new_child)?;

                // Update the root
                if is_root {
                    current_root.compressed_update(inner.commitments, new_x_coords, child_index)?;
                }

                even_new_child = CompressedChildCommitments::Inner(inner.commitments);
                self.nodes.insert(location, inner);
            } else {
                let mut inner = CompressedInner::default_odd();
                let new_x_coords = U::update_node(&mut inner, child_index, None, even_new_child)?;

                // Update the root
                if is_root {
                    current_root.compressed_update(inner.commitments, new_x_coords, child_index)?;
                }

                odd_new_child = CompressedChildCommitments::Inner(inner.commitments);
                self.nodes.insert(location, inner);
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
        new_leaf_value: CompressedLeafValue<C>,
        current_root: &mut CompressedCurveTreeRoot<L, M, C>,
    ) -> Result<(), Error> {
        self.batch_append_leaves(&[new_leaf_value], current_root, None)
    }

    pub fn batch_append_leaves(
        &mut self,
        leaves: &[CompressedLeafValue<C>],
        current_root: &mut CompressedCurveTreeRoot<L, M, C>,
        mut updated_nodes: Option<&mut BTreeMap<NodeLocation<L>, CompressedInner<M, C>>>,
    ) -> Result<(), Error> {
        let leaf_index_base = self.next_leaf_index;
        let mut leaf_idx = 0;
        let leaf_count = leaves.len() as LeafIndex;
        self.next_leaf_index += leaf_count;

        while leaf_idx < leaf_count {
            let leaf_value = leaves[leaf_idx as usize];

            let mut even_old_child = None;
            let mut even_new_child = CompressedChildCommitments::Leaf(leaf_value.into());
            let mut odd_old_child = None;
            let mut odd_new_child = CompressedChildCommitments::zero::<C::P1>();

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
                let node = self
                    .nodes
                    .entry(location)
                    .and_modify(|node| {
                        // Save the old commitments for the next level up.
                        if node.is_even {
                            even_old_child =
                                Some(CompressedChildCommitments::Inner(node.commitments));
                        } else {
                            odd_old_child =
                                Some(CompressedChildCommitments::Inner(node.commitments));
                        }
                    })
                    .or_insert_with(|| {
                        is_new_node = true;
                        if location.is_even() {
                            even_old_child = None;
                            // Create a new even node with zero commitments.
                            CompressedInner::default_even()
                        } else {
                            odd_old_child = None;
                            // Create a new odd node with zero commitments.
                            CompressedInner::default_odd()
                        }
                    });

                if node.is_even {
                    let new_x_coords =
                        U::update_node(node, child_index, odd_old_child, odd_new_child)?;

                    // Update the root
                    if is_root {
                        current_root.compressed_update(
                            node.commitments,
                            new_x_coords,
                            child_index,
                        )?;
                    }

                    // Save the new commitments for the next level up.
                    even_new_child = CompressedChildCommitments::Inner(node.commitments);
                } else {
                    let new_x_coords =
                        U::update_node(node, child_index, even_old_child, even_new_child)?;

                    // Update the root
                    if is_root {
                        current_root.compressed_update(
                            node.commitments,
                            new_x_coords,
                            child_index,
                        )?;
                    }

                    // If the child was a leaf, we may need to commit multiple leaves to this node.
                    if child_is_leaf {
                        // Try to commit as many leaves as possible to this node.
                        while child_index < L as ChildIndex - 1 && leaf_idx < leaf_count {
                            // Commit the next child leaf.
                            child_index += 1;
                            // Get the next uncommitted leaf.
                            let leaf_value = leaves[leaf_idx as usize];
                            even_old_child = None;
                            even_new_child = CompressedChildCommitments::leaf(leaf_value);
                            leaf_idx += 1;

                            let new_x_coords =
                                U::update_node(node, child_index, even_old_child, even_new_child)?;

                            // Update the root
                            if is_root {
                                current_root.compressed_update(
                                    node.commitments,
                                    new_x_coords,
                                    child_index,
                                )?;
                            }
                        }

                        // We have committed all possible leaves to this node.
                        // Clear this flag before updating the parent.
                        child_is_leaf = false;
                    }

                    // Save the new commitments for the next level up.
                    odd_new_child = CompressedChildCommitments::Inner(node.commitments);
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
    fn update_node(
        inner: &mut CompressedInner<M, C>,
        child_index: ChildIndex,
        old_child: Option<CompressedChildCommitments<M>>,
        new_child: CompressedChildCommitments<M>,
    ) -> Result<CompressedXCoords<M>, Error>;
}

/// Curve tree updater that helps updating the tree root when a leaf is added or updated.
#[derive(Clone, Default)]
pub struct DefaultCurveTreeUpdater<const L: usize, const M: usize, C: CurveTreeConfig> {
    _marker: PhantomData<C>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeUpdater<L, M, C>
    for DefaultCurveTreeUpdater<L, M, C>
{
    fn update_node(
        inner: &mut CompressedInner<M, C>,
        child_index: ChildIndex,
        old_child: Option<CompressedChildCommitments<M>>,
        new_child: CompressedChildCommitments<M>,
    ) -> Result<CompressedXCoords<M>, Error> {
        let params = C::parameters();

        let mut tmp_inner = inner.decompress()?;
        let new_x_coords = match &mut tmp_inner {
            Inner::Even(commitments) => {
                // Decompress the old and new child commitments.
                let old_child = old_child.map(|c| c.decompress::<C::P1>()).transpose()?;
                let new_child = new_child.decompress::<C::P1>()?;

                // Update the node.
                let new_x_coords = update_inner_node::<L, M, C::P1, C::P0>(
                    commitments,
                    child_index,
                    old_child,
                    new_child,
                    &params.odd_parameters.delta,
                    &params.even_parameters,
                )?;

                CompressedXCoords::compress::<C::P1>(&new_x_coords)?
            }
            Inner::Odd(commitments) => {
                // Decompress the old and new child commitments.
                let old_child = old_child.map(|c| c.decompress::<C::P0>()).transpose()?;
                let new_child = new_child.decompress::<C::P0>()?;

                // Update the node.
                let new_x_coords = update_inner_node::<L, M, C::P0, C::P1>(
                    commitments,
                    child_index,
                    old_child,
                    new_child,
                    &params.even_parameters.delta,
                    &params.odd_parameters,
                )?;

                CompressedXCoords::compress::<C::P0>(&new_x_coords)?
            }
        };

        // Update the compressed inner node.
        *inner = CompressedInner::compress(&tmp_inner)?;

        Ok(new_x_coords)
    }
}
