use std::collections::HashMap;

use curve_tree_relations::curve_tree::{CurveTree, Root, SelRerandParameters};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::lean_curve_tree::LeanCurveTree;
use curve_tree_relations::partial_curve_tree::PartialCurveTree;

use super::*;

pub type CurveTreeParameters = SelRerandParameters<PallasParameters, VestaParameters>;
pub type CurveTreeRoot<const L: usize> = Root<L, 1, PallasParameters, VestaParameters>;
pub type CurveTreePath<const L: usize> = CurveTreeWitnessPath<L, PallasParameters, VestaParameters>;

/// A trait for looking up paths in a curve tree.
pub trait CurveTreeLookup<const L: usize> {
    /// Returns the path to a leaf in the curve tree by its index.
    fn get_path_to_leaf_index(&self, leaf_index: u64) -> Result<CurveTreePath<L>>;

    /// Returns the path to a leaf in the curve tree by its value.
    fn get_path_to_leaf(&self, leaf: PallasA) -> Result<CurveTreePath<L>>;

    /// Returns the parameters of the curve tree.
    fn params(&self) -> &CurveTreeParameters;

    /// Returns the root node of the curve tree.
    fn root_node(&self) -> CurveTreeRoot<L>;
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

/// A Full Curve Tree that support both insertion and updates.
pub struct FullCurveTree<const L: usize> {
    tree: CurveTree<L, 1, PallasParameters, VestaParameters>,
    height: usize,
    leaves: Vec<PallasA>,
    length: usize,
    params: CurveTreeParameters,
}

impl<const L: usize> std::fmt::Debug for FullCurveTree<L> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FullCurveTree")
            .field("tree", &self.tree)
            .field("height", &self.height)
            .field("length", &self.length)
            .field("leaves", &self.leaves)
            .finish()
    }
}

impl<const L: usize> FullCurveTree<L> {
    /// Creates a new instance of `FullCurveTree` with the given height and generators length.
    pub fn new_with_capacity(cap: usize, height: usize, gens_length: usize) -> Self {
        let params = SelRerandParameters::new(gens_length, gens_length);
        let leaves = (0..cap).map(|_| PallasA::zero()).collect::<Vec<_>>();
        Self {
            tree: CurveTree::from_leaves(&leaves, &params, Some(height)),
            leaves,
            length: 0,
            height,
            params,
        }
    }

    pub fn height(&self) -> usize {
        self.tree.height()
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: PallasA) -> Result<usize> {
        let leaf_index = self.length;
        self.update(leaf, leaf_index)?;

        self.length += 1;

        Ok(leaf_index)
    }

    /// Updates an existing leaf in the curve tree.
    pub fn update(&mut self, leaf: PallasA, leaf_index: usize) -> Result<()> {
        let cap = self.leaves.len();
        if leaf_index >= cap {
            self.grow(leaf_index);
        }

        match self.leaves.get_mut(leaf_index) {
            Some(old_leaf) => {
                *old_leaf = leaf;
            }
            None => {
                return Err(Error::LeafNotFound(leaf));
            }
        }
        self.tree.update_leaf(leaf_index, 0, leaf, &self.params);
        Ok(())
    }

    /// Grows the leaves vector to accommodate more leaves.
    pub fn grow(&mut self, last_leaf_index: usize) {
        if last_leaf_index < self.leaves.len() {
            return;
        }
        let new_cap = last_leaf_index + 1;
        self.leaves.resize(new_cap, PallasA::zero());
        let new_tree = CurveTree::from_leaves(&self.leaves, &self.params, Some(self.height));
        self.tree = new_tree;
    }

    /// Returns the path to a leaf in the curve tree by its index.
    pub fn get_path_to_leaf_index(&self, leaf_index: usize) -> Result<CurveTreePath<L>> {
        Ok(self.tree.get_path_to_leaf_for_proof(leaf_index, 0))
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters {
        &self.params
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> CurveTreeRoot<L> {
        self.tree.root_node()
    }
}

/// A Curve Tree for the Verifier in the Dart BP protocol.
///
/// This tree is used to verify the commitments and proofs generated by the Prover.
///
/// It is a lean version of the curve tree, which means it does not store the full tree structure,
pub struct VerifierCurveTree<const L: usize> {
    lean_tree: LeanCurveTree<L, PallasParameters, VestaParameters>,
    params: CurveTreeParameters,
}

impl<const L: usize> VerifierCurveTree<L> {
    /// Creates a new instance of `VerifierCurveTree` with the given height and generators length.
    pub fn new(height: u8, gens_length: usize) -> Result<Self> {
        let params = SelRerandParameters::new(gens_length, gens_length);
        let lean_tree = LeanCurveTree::<L, PallasParameters, VestaParameters>::new(height, &params);
        Ok(Self { lean_tree, params })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: PallasA) {
        self.lean_tree.insert(leaf, &self.params);
    }

    /// Returns the parameters of the curve tree.
    pub fn params(&self) -> &CurveTreeParameters {
        &self.params
    }

    /// Get the root node of the curve tree.
    pub fn root_node(&self) -> CurveTreeRoot<L> {
        self.lean_tree.root_node()
    }
}

/// A Curve Tree for the Prover in the Dart BP protocol.
pub struct ProverCurveTree<const L: usize> {
    lean_tree: LeanCurveTree<L, PallasParameters, VestaParameters>,
    partial_tree: PartialCurveTree<L, PallasParameters, VestaParameters>,
    leaf_to_index: HashMap<PallasA, u64>,
    params: CurveTreeParameters,
}

impl<const L: usize> ProverCurveTree<L> {
    /// Creates a new instance of `ProverCurveTree` with the given height and generators length.
    pub fn new(height: u8, gens_length: usize) -> Result<Self> {
        let params = SelRerandParameters::new(gens_length, gens_length);
        // TODO: Needs to be filled or recreated from onchain state.
        let lean_tree = LeanCurveTree::<L, PallasParameters, VestaParameters>::new(height, &params);
        let partial_tree =
            PartialCurveTree::<L, PallasParameters, VestaParameters>::new(height, &params)?;
        Ok(Self {
            lean_tree,
            partial_tree,
            params,
            leaf_to_index: HashMap::new(),
        })
    }

    /// Insert a new leaf into the curve tree.
    pub fn insert(&mut self, leaf: PallasA) -> Result<u64> {
        self.lean_tree.insert(leaf, &self.params);
        let leaf_index = self.partial_tree.next_leaf_index;
        self.partial_tree.insert_leaf(
            leaf_index,
            leaf,
            self.lean_tree.odd_level_path_nodes.clone(),
            self.lean_tree.even_level_path_nodes.clone(),
        )?;
        self.leaf_to_index.insert(leaf, leaf_index);
        Ok(leaf_index)
    }

    /// Apply updates to the curve tree by inserting multiple untracked leaves.
    pub fn apply_updates(&mut self, leaves: Vec<PallasA>) -> Result<()> {
        for leaf in &leaves {
            self.lean_tree.insert(*leaf, &self.params);
        }
        self.partial_tree.update_on_leaves(leaves, &self.params)?;
        Ok(())
    }
}

impl<const L: usize> CurveTreeLookup<L> for &ProverCurveTree<L> {
    fn get_path_to_leaf_index(&self, leaf_index: u64) -> Result<CurveTreePath<L>> {
        Ok(self.partial_tree.get_path_to_leaf(leaf_index)?)
    }

    fn get_path_to_leaf(&self, leaf: PallasA) -> Result<CurveTreePath<L>> {
        if let Some(&leaf_index) = self.leaf_to_index.get(&leaf) {
            self.get_path_to_leaf_index(leaf_index)
        } else {
            Err(Error::LeafNotFound(leaf))
        }
    }

    fn params(&self) -> &CurveTreeParameters {
        &self.params
    }

    fn root_node(&self) -> CurveTreeRoot<L> {
        self.partial_tree.root_node()
    }
}
