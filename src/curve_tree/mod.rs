use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
#[cfg(feature = "std")]
use ark_std::collections::HashMap;
use ark_std::{Zero, vec::Vec};

pub use curve_tree_relations::{
    curve_tree::{Root, RootNode, SelRerandParameters},
    curve_tree_prover::{CurveTreeWitnessPath, WitnessNode},
};

use codec::{Decode, Encode};
use scale_info::TypeInfo;

use super::*;
use crate::curve_tree::{LeafIndex, NodeLevel};

pub mod backends;
pub use backends::*;

#[macro_use]
mod common;
pub use common::*;

#[derive(Debug, Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct WrappedCurveTreeParameters(Vec<u8>);

impl WrappedCurveTreeParameters {
    pub fn new(gens_length: usize) -> Result<Self, Error> {
        let params = CurveTreeParameters::new(gens_length, gens_length);
        let mut buf = Vec::new();
        params.serialize_uncompressed(&mut buf)?;
        Ok(Self(buf))
    }

    /// Decodes the wrapped value back into its original type `T`.
    pub fn decode(&self) -> Result<SelRerandParameters<PallasParameters, VestaParameters>, Error> {
        Ok(CurveTreeParameters::deserialize_uncompressed_unchecked(
            &self.0[..],
        )?)
    }
}

pub type CurveTreeParameters = SelRerandParameters<PallasParameters, VestaParameters>;
pub type CurveTreePath<const L: usize> = CurveTreeWitnessPath<L, PallasParameters, VestaParameters>;

#[derive(Debug, Clone, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(L))]
pub struct CurveTreeRoot<const L: usize>(
    pub WrappedCanonical<Root<L, 1, PallasParameters, VestaParameters>>,
);

impl<const L: usize> CurveTreeRoot<L> {
    pub fn new(root: &Root<L, 1, PallasParameters, VestaParameters>) -> Result<Self, Error> {
        Ok(Self(WrappedCanonical::wrap(root)?))
    }

    /// Decodes the wrapped value back into its original type `T`.
    pub fn decode(&self) -> Result<Root<L, 1, PallasParameters, VestaParameters>, Error> {
        self.0.decode()
    }
}

#[cfg(feature = "async_tree")]
impl_curve_tree_with_backend!(Async, AsyncCurveTreeWithBackend, AsyncCurveTreeBackend);
impl_curve_tree_with_backend!(Sync, CurveTreeWithBackend, CurveTreeBackend);

/// A trait for looking up paths in a curve tree.
pub trait CurveTreeLookup<const L: usize> {
    /// Returns the path to a leaf in the curve tree by its index.
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error>;

    /// Returns the path to a leaf in the curve tree by its value.
    fn get_path_to_leaf(
        &self,
        leaf: LeafValue<PallasParameters>,
    ) -> Result<CurveTreePath<L>, Error>;

    /// Returns the parameters of the curve tree.
    fn params(&self) -> &CurveTreeParameters;

    /// Returns the root node of the curve tree.
    fn root_node(&self) -> Result<CurveTreeRoot<L>, Error>;
}

/// Check if the tree root is valid.
///
/// This allows verifying proofs against older tree roots.
pub trait ValidateCurveTreeRoot<const L: usize> {
    /// Validates the root of the curve tree.
    fn validate_root(&self, root: &CurveTreeRoot<L>) -> bool;

    /// Returns the parameters of the curve tree.
    fn params(&self) -> &CurveTreeParameters;
}

pub struct RootHistory<const L: usize> {
    roots: Vec<CurveTreeRoot<L>>,
    history_length: usize,
    params: CurveTreeParameters,
}

impl<const L: usize> RootHistory<L> {
    /// Creates a new instance of `RootHistory` with the given history length and parameters.
    pub fn new(history_length: usize, params: &CurveTreeParameters) -> Self {
        Self {
            roots: Vec::with_capacity(history_length),
            history_length,
            params: params.clone(),
        }
    }

    /// Adds a new root to the history.
    pub fn add_root(&mut self, root: CurveTreeRoot<L>) {
        if self.roots.len() >= self.history_length {
            self.roots.remove(0);
        }
        self.roots.push(root);
    }
}

impl<const L: usize> ValidateCurveTreeRoot<L> for &RootHistory<L> {
    fn validate_root(&self, root: &CurveTreeRoot<L>) -> bool {
        self.roots.contains(root)
    }

    fn params(&self) -> &CurveTreeParameters {
        &self.params
    }
}

pub struct FullCurveTree<const L: usize> {
    tree: CurveTreeWithBackend<L, 1, PallasParameters, VestaParameters>,
}

impl<const L: usize> FullCurveTree<L> {
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
    pub fn insert(&mut self, leaf: LeafValue<PallasParameters>) -> Result<LeafIndex, Error> {
        self.tree.insert_leaf(leaf)
    }

    /// Updates an existing leaf in the curve tree.
    pub fn update(
        &mut self,
        leaf: LeafValue<PallasParameters>,
        leaf_index: LeafIndex,
    ) -> Result<(), Error> {
        self.tree.update_leaf(leaf_index, leaf)
    }

    /// Returns the path to a leaf in the curve tree by its index.
    pub fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error> {
        Ok(self.tree.get_path_to_leaf(leaf_index, 0)?)
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters {
        self.tree.parameters()
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(CurveTreeRoot::new(&self.tree.root_node()?)?)
    }
}

impl<const L: usize> CurveTreeLookup<L> for &FullCurveTree<L> {
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error> {
        Ok(self.tree.get_path_to_leaf(leaf_index, 0)?)
    }

    fn get_path_to_leaf(
        &self,
        leaf: LeafValue<PallasParameters>,
    ) -> Result<CurveTreePath<L>, Error> {
        Err(Error::LeafNotFound(leaf))
    }

    fn params(&self) -> &CurveTreeParameters {
        self.tree.parameters()
    }

    fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(CurveTreeRoot::new(&self.tree.root_node()?)?)
    }
}

/// A Curve Tree for the Verifier in the Dart BP protocol.
///
/// This tree is used to verify the commitments and proofs generated by the Prover.
///
/// It is a lean version of the curve tree, which means it does not store the full tree structure,
pub struct VerifierCurveTree<const L: usize> {
    tree: CurveTreeWithBackend<L, 1, PallasParameters, VestaParameters>,
}

impl<const L: usize> VerifierCurveTree<L> {
    /// Creates a new instance of `VerifierCurveTree` with the given height and generators length.
    pub fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Error> {
        Ok(Self {
            tree: CurveTreeWithBackend::new(height, gens_length)?,
        })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: LeafValue<PallasParameters>) -> Result<LeafIndex, Error> {
        self.tree.insert_leaf(leaf.into())
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters {
        self.tree.parameters()
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(CurveTreeRoot::new(&self.tree.root_node()?)?)
    }
}

/// A Curve Tree for the Prover in the Dart BP protocol.
#[cfg(feature = "std")]
pub struct ProverCurveTree<const L: usize> {
    tree: CurveTreeWithBackend<L, 1, PallasParameters, VestaParameters>,
    leaf_to_index: HashMap<LeafValue<PallasParameters>, u64>,
}

#[cfg(feature = "std")]
impl<const L: usize> ProverCurveTree<L> {
    /// Creates a new instance of `ProverCurveTree` with the given height and generators length.
    pub fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Error> {
        Ok(Self {
            tree: CurveTreeWithBackend::new(height, gens_length)?,
            leaf_to_index: HashMap::new(),
        })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: LeafValue<PallasParameters>) -> Result<u64, Error> {
        let leaf_index = self.tree.insert_leaf(leaf)? as u64;
        self.leaf_to_index.insert(leaf, leaf_index);
        Ok(leaf_index)
    }

    /// Apply updates to the curve tree by inserting multiple untracked leaves.
    pub fn apply_updates(&mut self, leaves: Vec<LeafValue<PallasParameters>>) -> Result<(), Error> {
        for leaf in &leaves {
            self.tree.insert_leaf(*leaf)?;
        }
        Ok(())
    }
}

#[cfg(feature = "std")]
impl<const L: usize> CurveTreeLookup<L> for &ProverCurveTree<L> {
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error> {
        Ok(self.tree.get_path_to_leaf(leaf_index, 0)?)
    }

    fn get_path_to_leaf(
        &self,
        leaf: LeafValue<PallasParameters>,
    ) -> Result<CurveTreePath<L>, Error> {
        if let Some(&leaf_index) = self.leaf_to_index.get(&leaf) {
            self.get_path_to_leaf_index(leaf_index)
        } else {
            Err(Error::LeafNotFound(leaf))
        }
    }

    fn params(&self) -> &CurveTreeParameters {
        self.tree.parameters()
    }

    fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(CurveTreeRoot::new(&self.tree.root_node()?)?)
    }
}
