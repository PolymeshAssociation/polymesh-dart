use std::collections::HashMap;

use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_std::Zero;
use curve_tree_relations::{
    curve_tree::{Root, RootNode, SelRerandParameters},
    curve_tree_prover::{CurveTreeWitnessPath, WitnessNode},
    single_level_select_and_rerandomize::*,
};

use crate::error::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum NodeLocation<const L: usize> {
    Leaf(usize), // Leaf nodes are identified by their index
    Odd {
        level: usize, // Level of the node in the tree
        index: usize, // Index of the node at that level
    },
    Even {
        level: usize, // Level of the node in the tree
        index: usize, // Index of the node at that level
    },
}

impl<const L: usize> NodeLocation<L> {
    /// Creates a leaf node location.
    pub fn leaf(leaf_index: usize) -> Self {
        // Leaf nodes are at level 0, and their index is the leaf_index
        Self::Leaf(leaf_index)
    }

    pub fn root(height: usize) -> Self {
        // Root nodes are at the highest level, which is `height`, and their index is 0
        if height % 2 == 0 {
            // Even height, root is an even node
            Self::Even {
                level: height,
                index: 0,
            }
        } else {
            // Odd height, root is an odd node
            Self::Odd {
                level: height,
                index: 0,
            }
        }
    }

    /// Returns true if the node is a leaf node.
    pub fn is_leaf(&self) -> bool {
        matches!(self, Self::Leaf(_))
    }

    /// Returns true if the node is an odd node.
    pub fn is_odd(&self) -> bool {
        matches!(self, Self::Odd { .. })
    }

    /// Returns true if the node is an even node.
    pub fn is_even(&self) -> bool {
        !self.is_odd()
    }

    /// Returns true if the node is the root of the tree at the given height.
    /// A node is a root if it is at the highest level and has index 0.
    pub fn is_root(&self, height: usize) -> bool {
        match *self {
            Self::Leaf(_) => false,
            Self::Odd { level, index } | Self::Even { level, index } => {
                // A node is a root if it is at the highest level and has index 0
                level >= height && index == 0
            }
        }
    }

    /// Returns the level of the node.
    ///
    /// Leaf nodes are at level 0, odd nodes are at their specified level, and even nodes are at their specified level.
    pub fn level(&self) -> usize {
        match *self {
            Self::Leaf(_) => 0,
            Self::Odd { level, .. } | Self::Even { level, .. } => level,
        }
    }

    /// Returns the index of the node at its level.
    pub fn index(&self) -> usize {
        match *self {
            Self::Leaf(leaf_index) => leaf_index,
            Self::Odd { index, .. } | Self::Even { index, .. } => index,
        }
    }

    /// Returns the parent node location of this node.
    ///
    /// The parent is one level up, and its index is the integer division of the current index by L.
    pub fn parent(self) -> (Self, usize) {
        match self {
            Self::Leaf(leaf_index) => (
                Self::Odd {
                    level: 1,
                    index: leaf_index.saturating_div(L),
                },
                leaf_index % L,
            ),
            Self::Odd { level, index } => (
                Self::Even {
                    level: level.saturating_add(1),
                    index: index.saturating_div(L),
                },
                index % L,
            ),
            Self::Even { level, index } => (
                Self::Odd {
                    level: level.saturating_add(1),
                    index: index.saturating_div(L),
                },
                index % L,
            ),
        }
    }

    /// Returns the child node location of this node at the given child index.
    ///
    /// The child index must be less than L, and the child node is at one level down.
    /// The index of the child node is the current index multiplied by L plus the child index.
    pub fn child(self, child_index: usize) -> Result<Self> {
        if child_index >= L {
            return Err(Error::CurveTreeInvalidChildIndex(child_index));
        }
        match self {
            Self::Leaf(_) => {
                // Leaf nodes cannot have children, so we return an error.
                Err(Error::CurveTreeLeafCannotHaveChildren)
            }
            Self::Odd { level: 1, index } => Ok(Self::Leaf(index * L + child_index)),
            Self::Odd { level, index } => Ok(Self::Even {
                level: level.saturating_sub(1),
                index: index * L + child_index,
            }),
            Self::Even { level, index } => Ok(Self::Odd {
                level: level.saturating_sub(1),
                index: index * L + child_index,
            }),
        }
    }
}

fn default_inner_node<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
>(
    old_child: Option<ChildCommitments<M, P0>>,
    delta: &Affine<P0>,
    parameters: &SingleLayerParameters<P1>,
) -> [Affine<P1>; M] {
    // Create an array of commitments for the inner node.
    let mut commitments = [Affine::<P1>::zero(); M];
    for (tree_index, commitment) in commitments.iter_mut().enumerate() {
        let mut x_coords = [P0::BaseField::zero(); L];
        if let Some(old_comm) = old_child {
            x_coords[0] = (old_comm.commitment(tree_index) + delta).into_affine().x;
        }
        *commitment = parameters.commit(&x_coords, P1::ScalarField::zero(), tree_index)
    }
    commitments
}

fn update_inner_node<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
>(
    commitments: &mut [Affine<P1>; M],
    local_index: usize,
    old_child: Option<ChildCommitments<M, P0>>,
    new_child: ChildCommitments<M, P0>,
    delta: &Affine<P0>,
    parameters: &SingleLayerParameters<P1>,
) {
    for tree_index in 0..M {
        let old_x_coord = if let Some(old_comm) = old_child {
            (old_comm.commitment(tree_index) + delta).into_affine().x
        } else {
            P0::BaseField::zero()
        };
        let new_x_coord = (new_child.commitment(tree_index) + delta).into_affine().x;
        let gen_iter = parameters
            .bp_gens
            .share(0)
            .G(L * (tree_index + 1))
            .skip(L * tree_index + local_index);
        let g = gen_iter.copied().next().unwrap();
        commitments[tree_index] =
            (commitments[tree_index].into_group() + g * (new_x_coord - old_x_coord)).into_affine();
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ChildCommitments<const M: usize, P0: SWCurveConfig> {
    Leaf(Affine<P0>),
    Inner([Affine<P0>; M]),
}

impl<const M: usize, P0: SWCurveConfig + Copy + Send> ChildCommitments<M, P0> {
    pub fn leaf(leaf: Affine<P0>) -> Self {
        ChildCommitments::Leaf(leaf)
    }

    pub fn inner(commitments: [Affine<P0>; M]) -> Self {
        ChildCommitments::Inner(commitments)
    }

    pub fn commitment(&self, tree_index: usize) -> Affine<P0> {
        match self {
            ChildCommitments::Leaf(leaf) => *leaf,
            ChildCommitments::Inner(commitments) => commitments[tree_index],
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Inner<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    Even([Affine<P0>; M]),
    Odd([Affine<P1>; M]),
}

impl<
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> std::fmt::Debug for Inner<M, P0, P1>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Inner::Even(commitment) => write!(f, "Even({:?})", commitment),
            Inner::Odd(commitment) => write!(f, "Odd({:?})", commitment),
        }
    }
}

impl<
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> Inner<M, P0, P1>
{
    pub fn default_even<const L: usize>(
        old_child: Option<ChildCommitments<M, P1>>,
        delta: &Affine<P1>,
        parameters: &SingleLayerParameters<P0>,
    ) -> Self {
        Self::Even(default_inner_node::<L, M, P1, P0>(
            old_child, delta, parameters,
        ))
    }

    pub fn default_odd<const L: usize>(
        old_child: Option<ChildCommitments<M, P0>>,
        delta: &Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) -> Self {
        Self::Odd(default_inner_node::<L, M, P0, P1>(
            old_child, delta, parameters,
        ))
    }

    pub fn update_even_node<const L: usize>(
        commitments: &mut [Affine<P0>; M],
        local_index: usize,
        old_child: Option<ChildCommitments<M, P1>>,
        new_child: ChildCommitments<M, P1>,
        delta: &Affine<P1>,
        parameters: &SingleLayerParameters<P0>,
    ) {
        update_inner_node::<L, M, P1, P0>(
            commitments,
            local_index,
            old_child,
            new_child,
            delta,
            parameters,
        );
    }

    pub fn update_odd_node<const L: usize>(
        commitments: &mut [Affine<P1>; M],
        local_index: usize,
        old_child: Option<ChildCommitments<M, P0>>,
        new_child: ChildCommitments<M, P0>,
        delta: &Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) {
        update_inner_node::<L, M, P0, P1>(
            commitments,
            local_index,
            old_child,
            new_child,
            delta,
            parameters,
        );
    }
}

pub struct CurveTreeStorage<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    pub height: usize,
    pub leafs: Vec<Affine<P0>>,
    next_leaf_index: usize,
    pub nodes: HashMap<NodeLocation<L>, Inner<M, P0, P1>>,
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> std::fmt::Debug for CurveTreeStorage<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_struct("CurveTreeStorage")
            .field("height", &self.height)
            .field("leafs", &self.leafs)
            .field("next_leaf_index", &self.next_leaf_index)
            .field("nodes", &self.nodes)
            .finish()
    }
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> CurveTreeStorage<L, M, P0, P1>
{
    pub fn new(height: usize, parameters: &SelRerandParameters<P0, P1>) -> Result<Self> {
        let mut tree = Self {
            height,
            leafs: vec![],
            next_leaf_index: 0,
            nodes: HashMap::new(),
        };
        tree.update_leaf(0, Self::default_leaf_value(), parameters)?;
        Ok(tree)
    }

    pub fn height(&self) -> usize {
        self.height
    }

    fn default_leaf_value() -> Affine<P0> {
        Affine::<P0>::zero()
    }

    pub fn insert_leaf(
        &mut self,
        leaf_value: Affine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<()> {
        let leaf_index = self.next_leaf_index;
        self.next_leaf_index += 1;
        self.update_leaf(leaf_index, leaf_value, parameters)?;
        Ok(())
    }

    pub fn get_leaf(&self, leaf_index: usize) -> Option<Affine<P0>> {
        self.leafs.get(leaf_index).copied()
    }

    fn _get_odd_x_coord_children_batch(
        &self,
        parent: NodeLocation<L>,
        delta: &Affine<P1>,
    ) -> Result<Vec<[P1::BaseField; L]>> {
        let mut batch_x_coord_children = Vec::with_capacity(M);
        for tree_index in 0..M {
            let x_coord_children = self._get_odd_x_coord_children(tree_index, parent, delta)?;
            batch_x_coord_children.push(x_coord_children);
        }
        Ok(batch_x_coord_children)
    }

    fn _get_odd_x_coord_children(
        &self,
        tree_index: usize,
        parent: NodeLocation<L>,
        delta: &Affine<P1>,
    ) -> Result<[P1::BaseField; L]> {
        let mut x_coord_children = [P1::BaseField::zero(); L];
        for idx in 0..L {
            let child = parent.child(idx)?;
            let x_coord = match self.nodes.get(&child).copied() {
                Some(Inner::Odd(commitments)) => {
                    Some((commitments[tree_index] + delta).into_affine().x)
                }
                Some(Inner::Even(_)) => {
                    return Err(Error::CurveTreeInvalidChildNode {
                        level: child.level(),
                        index: child.index(),
                    });
                }
                None => None,
            };
            if let Some(x_coord) = x_coord {
                x_coord_children[idx] = x_coord;
            }
        }
        Ok(x_coord_children)
    }

    fn _get_even_x_coord_children_batch(
        &self,
        parent: NodeLocation<L>,
        delta: &Affine<P0>,
    ) -> Result<Vec<[P0::BaseField; L]>> {
        let mut batch_x_coord_children = Vec::with_capacity(M);
        for tree_index in 0..M {
            let x_coord_children = self._get_even_x_coord_children(tree_index, parent, delta)?;
            batch_x_coord_children.push(x_coord_children);
        }
        Ok(batch_x_coord_children)
    }

    fn _get_even_x_coord_children(
        &self,
        tree_index: usize,
        parent: NodeLocation<L>,
        delta: &Affine<P0>,
    ) -> Result<[P0::BaseField; L]> {
        let mut x_coord_children = [P0::BaseField::zero(); L];
        for idx in 0..L {
            let child = parent.child(idx)?;
            let commitment = if let NodeLocation::Leaf(leaf_index) = child {
                self.leafs.get(leaf_index).copied()
            } else {
                match self.nodes.get(&child).copied() {
                    Some(Inner::Even(commitments)) => Some(commitments[tree_index]),
                    Some(Inner::Odd(_)) => {
                        log::error!("An Odd node cannot have an odd child");
                        return Err(Error::CurveTreeInvalidChildNode {
                            level: child.level(),
                            index: child.index(),
                        });
                    }
                    None => None,
                }
            };
            if let Some(commitment) = commitment {
                x_coord_children[idx] = (commitment + delta).into_affine().x;
            }
        }
        Ok(x_coord_children)
    }

    pub fn root_node(
        &self,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Root<L, M, P0, P1>> {
        let root = NodeLocation::<L>::root(self.height);
        match self.nodes.get(&root) {
            Some(Inner::Even(commitments)) => Ok(Root::Even(RootNode {
                commitments: commitments.clone(),
                x_coord_children: self
                    ._get_odd_x_coord_children_batch(root, &parameters.odd_parameters.delta)?,
            })),
            Some(Inner::Odd(commitments)) => Ok(Root::Odd(RootNode {
                commitments: commitments.clone(),
                x_coord_children: self
                    ._get_even_x_coord_children_batch(root, &parameters.even_parameters.delta)?,
            })),
            None => Err(Error::CurveTreeRootNotFound),
        }
    }

    pub fn get_path_to_leaf(
        &self,
        leaf_index: usize,
        tree_index: usize,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<CurveTreeWitnessPath<L, P0, P1>> {
        let mut even_internal_nodes = Vec::with_capacity(self.height);
        let mut odd_internal_nodes = Vec::with_capacity(self.height);

        let mut even_child = *self
            .leafs
            .get(leaf_index)
            .ok_or_else(|| Error::CurveTreeLeafIndexOutOfBounds(leaf_index))?;
        let mut odd_child = Affine::<P1>::zero();

        // Start at the leaf's location.
        let mut location = NodeLocation::<L>::leaf(leaf_index);

        while !location.is_root(self.height) {
            let (parent_location, _) = location.parent();
            let node =
                self.nodes
                    .get(&parent_location)
                    .ok_or_else(|| Error::CurveTreeNodeNotFound {
                        level: parent_location.level(),
                        index: parent_location.index(),
                    })?;

            match node {
                Inner::Even(commitments) => {
                    even_child = commitments[tree_index];
                    even_internal_nodes.push(WitnessNode {
                        x_coord_children: self._get_odd_x_coord_children(
                            tree_index,
                            parent_location,
                            &parameters.odd_parameters.delta,
                        )?,
                        child_node_to_randomize: odd_child,
                    });
                }
                Inner::Odd(commitments) => {
                    odd_child = commitments[tree_index];
                    odd_internal_nodes.push(WitnessNode {
                        x_coord_children: self._get_even_x_coord_children(
                            tree_index,
                            parent_location,
                            &parameters.even_parameters.delta,
                        )?,
                        child_node_to_randomize: even_child,
                    });
                }
            }
            location = parent_location;
        }

        even_internal_nodes.reverse();
        odd_internal_nodes.reverse();
        Ok(CurveTreeWitnessPath {
            even_internal_nodes,
            odd_internal_nodes,
        })
    }

    fn _set_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: Affine<P0>,
    ) -> Result<Option<Affine<P0>>> {
        let old_leaf_value = if let Some(leaf) = self.leafs.get_mut(leaf_index) {
            let old = *leaf;
            *leaf = new_leaf_value;
            Some(old)
        } else if leaf_index == self.leafs.len() {
            // If the leaf index is equal to the current length, we are adding a new leaf.
            self.leafs.push(new_leaf_value);
            None
        } else {
            return Err(Error::CurveTreeLeafIndexOutOfBounds(leaf_index));
        };
        Ok(old_leaf_value)
    }

    pub fn update_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: Affine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<()> {
        // Update the leaf to the new value and get the old value.
        let old_leaf_value = self._set_leaf(leaf_index, new_leaf_value)?;

        // Store the leaf as the even commitment.
        let mut even_old_child = old_leaf_value.map(ChildCommitments::leaf);
        let mut even_new_child = ChildCommitments::leaf(new_leaf_value);
        // Use zeroes to initialize the odd commitments.
        let mut odd_old_child = None;
        let mut odd_new_child = ChildCommitments::leaf(Affine::<P1>::zero());

        // Start at the leaf's location.
        let mut location = NodeLocation::<L>::leaf(leaf_index);

        // Keep going until we reach the root of the tree.
        while !location.is_root(self.height) {
            // Get the parent location and the child index of the current node.
            let (parent_location, child_index) = location.parent();

            use std::collections::hash_map::Entry;
            let (node, is_old) = match self.nodes.entry(parent_location) {
                Entry::Occupied(entry) => (entry.into_mut(), true),
                Entry::Vacant(entry) => {
                    // If the parent node does not exist, we need to create it.
                    // Depending on whether the parent location is even or odd, we create an even or odd
                    // node, using the old child values if they exist.
                    let node = if parent_location.is_even() {
                        entry.insert(Inner::default_even::<L>(
                            odd_old_child,
                            &parameters.odd_parameters.delta,
                            &parameters.even_parameters,
                        ))
                    } else {
                        entry.insert(Inner::default_odd::<L>(
                            even_old_child,
                            &parameters.even_parameters.delta,
                            &parameters.odd_parameters,
                        ))
                    };
                    (node, false)
                }
            };

            match node {
                Inner::Even(commitments) => {
                    // If the node is new, there is no old commitment value.
                    // This old commitment value is used when updating the parent node.
                    even_old_child = is_old.then(|| ChildCommitments::inner(*commitments));

                    // Update the node.  We pass both the old and new child commitments.
                    Inner::<M, _, _>::update_even_node::<L>(
                        commitments,
                        child_index,
                        odd_old_child,
                        odd_new_child,
                        &parameters.odd_parameters.delta,
                        &parameters.even_parameters,
                    );

                    // Save the new commitment value for updating the parent.
                    even_new_child = ChildCommitments::inner(*commitments);
                }
                Inner::Odd(commitments) => {
                    // If the node is new, there is no old commitment value.
                    // This old commitment value is used when updating the parent node.
                    odd_old_child = is_old.then(|| ChildCommitments::inner(*commitments));

                    // Update the node.  We pass both the old and new child commitments.
                    Inner::<M, _, _>::update_odd_node::<L>(
                        commitments,
                        child_index,
                        even_old_child,
                        even_new_child,
                        &parameters.even_parameters.delta,
                        &parameters.odd_parameters,
                    );

                    // Save the new commitment value for updating the parent.
                    odd_new_child = ChildCommitments::inner(*commitments);
                }
            }

            location = parent_location;
        }

        // Check if the tree has grown to accommodate the new leaf.
        // if the root's level is higher than the current height, we need to update the height.
        if location.level() > self.height {
            log::warn!(
                "Tree height increased from {} to {}",
                self.height,
                location.level()
            );
            self.height = location.level();
        }
        Ok(())
    }
}
