use std::collections::HashMap;
use std::ops::Deref;

use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::Zero;

use curve_tree_relations::{
    curve_tree::{Root, RootNode, SelRerandParameters},
    curve_tree_prover::{CurveTreeWitnessPath, WitnessNode},
};

use super::*;
use crate::curve_tree::{LeafIndex, NodeLevel};

pub mod backends;
pub use backends::*;

#[macro_use]
mod common;
pub use common::*;

pub type CurveTreeParameters = SelRerandParameters<PallasParameters, VestaParameters>;
pub type CurveTreePath<const L: usize> = CurveTreeWitnessPath<L, PallasParameters, VestaParameters>;

#[derive(Debug, Clone, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct CurveTreeRoot<const L: usize>(pub Root<L, 1, PallasParameters, VestaParameters>);

#[cfg(feature = "async_tree")]
impl_curve_tree_with_backend!(Async, AsyncCurveTreeWithBackend, AsyncCurveTreeBackend);
impl_curve_tree_with_backend!(Sync, CurveTreeWithBackend, CurveTreeBackend);

impl<const L: usize> Deref for CurveTreeRoot<L> {
    type Target = Root<L, 1, PallasParameters, VestaParameters>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const L: usize> From<Root<L, 1, PallasParameters, VestaParameters>> for CurveTreeRoot<L> {
    fn from(root: Root<L, 1, PallasParameters, VestaParameters>) -> Self {
        Self(root)
    }
}

/// A trait for looking up paths in a curve tree.
pub trait CurveTreeLookup<const L: usize> {
    /// Returns the path to a leaf in the curve tree by its index.
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error>;

    /// Returns the path to a leaf in the curve tree by its value.
    fn get_path_to_leaf(&self, leaf: PallasA) -> Result<CurveTreePath<L>, Error>;

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

impl<const L: usize> std::fmt::Debug for FullCurveTree<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FullCurveTreeStorage")
            .field("tree", &self.tree)
            .finish()
    }
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
    pub fn insert(&mut self, leaf: PallasA) -> Result<LeafIndex, Error> {
        self.tree.insert_leaf(leaf.into())
    }

    /// Updates an existing leaf in the curve tree.
    pub fn update(&mut self, leaf: PallasA, leaf_index: LeafIndex) -> Result<(), Error> {
        self.tree.update_leaf(leaf_index, leaf.into())
    }

    /// Returns the path to a leaf in the curve tree by its index.
    pub fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error> {
        Ok(self.tree.get_path_to_leaf(leaf_index, 0)?)
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters {
        &self.tree.parameters()
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(self.tree.root_node()?.into())
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
    pub fn insert(&mut self, leaf: PallasA) -> Result<LeafIndex, Error> {
        self.tree.insert_leaf(leaf.into())
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters {
        &self.tree.parameters()
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(self.tree.root_node()?.into())
    }
}

/// A Curve Tree for the Prover in the Dart BP protocol.
pub struct ProverCurveTree<const L: usize> {
    tree: CurveTreeWithBackend<L, 1, PallasParameters, VestaParameters>,
    leaf_to_index: HashMap<PallasA, u64>,
}

impl<const L: usize> ProverCurveTree<L> {
    /// Creates a new instance of `ProverCurveTree` with the given height and generators length.
    pub fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Error> {
        Ok(Self {
            tree: CurveTreeWithBackend::new(height, gens_length)?,
            leaf_to_index: HashMap::new(),
        })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: PallasA) -> Result<u64, Error> {
        let leaf_index = self.tree.insert_leaf(leaf.into())? as u64;
        self.leaf_to_index.insert(leaf, leaf_index);
        Ok(leaf_index)
    }

    /// Apply updates to the curve tree by inserting multiple untracked leaves.
    pub fn apply_updates(&mut self, leaves: Vec<PallasA>) -> Result<(), Error> {
        for leaf in &leaves {
            self.tree.insert_leaf(leaf.into())?;
        }
        Ok(())
    }
}

impl<const L: usize> CurveTreeLookup<L> for &ProverCurveTree<L> {
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error> {
        Ok(self.tree.get_path_to_leaf(leaf_index, 0)?)
    }

    fn get_path_to_leaf(&self, leaf: PallasA) -> Result<CurveTreePath<L>, Error> {
        if let Some(&leaf_index) = self.leaf_to_index.get(&leaf) {
            self.get_path_to_leaf_index(leaf_index)
        } else {
            Err(Error::LeafNotFound(leaf))
        }
    }

    fn params(&self) -> &CurveTreeParameters {
        &self.tree.parameters()
    }

    fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(self.tree.root_node()?.into())
    }
}
