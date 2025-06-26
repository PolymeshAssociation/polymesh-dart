use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_std::Zero;
use curve_tree_relations::{
    curve_tree::SelRerandParameters, single_level_select_and_rerandomize::*,
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

fn init_empty_inner_node<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
>(
    new_child: ChildCommitments<M, P0>,
    delta: &Affine<P0>,
    parameters: &SingleLayerParameters<P1>,
) -> [Affine<P1>; M] {
    let mut commitments = [Affine::<P1>::zero(); M];
    for tree_index in 0..M {
        let new_x_coord = (new_child.commitment(tree_index) + delta).into_affine().x;
        let gen_iter = parameters
            .bp_gens
            .share(0)
            .G(L * (tree_index + 1))
            .skip(L * tree_index);
        let g = gen_iter.copied().next().unwrap();
        commitments[tree_index] =
            (commitments[tree_index].into_group() + g * new_x_coord).into_affine();
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
    Leaf(LeafValue<P0>),
    Inner([Affine<P0>; M]),
}

impl<const M: usize, P0: SWCurveConfig + Copy + Send> ChildCommitments<M, P0> {
    pub fn leaf(leaf: LeafValue<P0>) -> Self {
        ChildCommitments::Leaf(leaf)
    }

    pub fn inner(commitments: [Affine<P0>; M]) -> Self {
        ChildCommitments::Inner(commitments)
    }

    pub fn commitment(&self, tree_index: usize) -> Affine<P0> {
        match self {
            ChildCommitments::Leaf(leaf) => leaf.0,
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
    pub fn init_empty_even<const L: usize>(
        new_child: ChildCommitments<M, P1>,
        delta: &Affine<P1>,
        parameters: &SingleLayerParameters<P0>,
    ) -> Self {
        Self::Even(init_empty_inner_node::<L, M, P1, P0>(
            new_child, delta, parameters,
        ))
    }

    pub fn init_empty_odd<const L: usize>(
        new_child: ChildCommitments<M, P0>,
        delta: &Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) -> Self {
        Self::Odd(init_empty_inner_node::<L, M, P0, P1>(
            new_child, delta, parameters,
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

/// This is used to share code between an async and sync version of the curve tree.
pub(crate) struct TreeUpdaterState<
    'a,
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> {
    even_new_child: ChildCommitments<M, P0>,
    odd_new_child: ChildCommitments<M, P1>,
    even_old_child: Option<ChildCommitments<M, P0>>,
    odd_old_child: Option<ChildCommitments<M, P1>>,
    height: usize,
    parameters: &'a SelRerandParameters<P0, P1>,
    location: NodeLocation<L>,
    child_index: usize,
}

impl<
    'a,
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> TreeUpdaterState<'a, L, M, P0, P1>
{
    pub fn new(
        leaf_index: usize,
        old_leaf_value: Option<LeafValue<P0>>,
        new_leaf_value: LeafValue<P0>,
        height: usize,
        parameters: &'a SelRerandParameters<P0, P1>,
    ) -> Result<Self> {
        // Store the leaf as the even commitment.
        let even_old_child = old_leaf_value.map(ChildCommitments::leaf);
        let even_new_child = ChildCommitments::leaf(new_leaf_value);
        // Use zeroes to initialize the odd commitments.
        let odd_old_child = None;
        let odd_new_child = ChildCommitments::leaf(LeafValue(Affine::<P1>::zero()));

        // Start at the leaf's location.
        let location = NodeLocation::<L>::leaf(leaf_index);

        Ok(Self {
            even_new_child,
            odd_new_child,
            even_old_child,
            odd_old_child,
            height,
            parameters,
            location,
            child_index: 0,
        })
    }

    pub fn is_new_height(&mut self) -> Option<usize> {
        let level = self.location.level();
        if level > self.height {
            log::warn!("Tree height increased from {} to {}", self.height, level);
            self.height = level;
            Some(level)
        } else {
            None
        }
    }

    pub fn is_root(&self) -> bool {
        self.location.is_root(self.height)
    }

    pub fn move_to_parent(&mut self) -> Result<NodeLocation<L>> {
        let (parent_location, child_index) = self.location.parent();
        self.location = parent_location;
        self.child_index = child_index;
        Ok(parent_location)
    }

    pub fn update_node(&mut self, node: Option<Inner<M, P0, P1>>) -> Result<Inner<M, P0, P1>> {
        match node {
            Some(mut node) => {
                match &mut node {
                    Inner::Even(commitments) => {
                        // We save the old commitment value for updating the parent node.
                        self.even_old_child = Some(ChildCommitments::inner(*commitments));

                        // Update the node.  We pass both the old and new child commitments.
                        Inner::<M, _, _>::update_even_node::<L>(
                            commitments,
                            self.child_index,
                            self.odd_old_child,
                            self.odd_new_child,
                            &self.parameters.odd_parameters.delta,
                            &self.parameters.even_parameters,
                        );

                        // Save the new commitment value for updating the parent.
                        self.even_new_child = ChildCommitments::inner(*commitments);
                    }
                    Inner::Odd(commitments) => {
                        // We save the old commitment value for updating the parent node.
                        self.odd_old_child = Some(ChildCommitments::inner(*commitments));

                        // Update the node.  We pass both the old and new child commitments.
                        Inner::<M, _, _>::update_odd_node::<L>(
                            commitments,
                            self.child_index,
                            self.even_old_child,
                            self.even_new_child,
                            &self.parameters.even_parameters.delta,
                            &self.parameters.odd_parameters,
                        );

                        // Save the new commitment value for updating the parent.
                        self.odd_new_child = ChildCommitments::inner(*commitments);
                    }
                }
                Ok(node)
            }
            None => {
                // If thsi node does not exist, we need to create it.
                let node = if self.location.is_even() {
                    // If the location is even, we create an even node.
                    Inner::init_empty_even::<L>(
                        self.odd_new_child,
                        &self.parameters.odd_parameters.delta,
                        &self.parameters.even_parameters,
                    )
                } else {
                    // If the location is odd, we create an odd node.
                    Inner::init_empty_odd::<L>(
                        self.even_new_child,
                        &self.parameters.even_parameters.delta,
                        &self.parameters.odd_parameters,
                    )
                };

                // Save the new commitment value for updating the parent.
                // Since this node is new, there isn't an old commitment value for it.
                match node {
                    Inner::Even(commitments) => {
                        self.even_old_child = None;
                        self.even_new_child = ChildCommitments::inner(commitments);
                    }
                    Inner::Odd(commitments) => {
                        self.odd_old_child = None;
                        self.odd_new_child = ChildCommitments::inner(commitments);
                    }
                }
                Ok(node)
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LeafValue<P0: SWCurveConfig>(pub(crate) Affine<P0>);

impl<P0: SWCurveConfig + Copy + Send> Default for LeafValue<P0> {
    fn default() -> Self {
        Self(Affine::<P0>::zero())
    }
}

impl<P0: SWCurveConfig + Copy + Send> std::fmt::Debug for LeafValue<P0> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "LeafValue({:?})", self.0)
    }
}

impl<P0: SWCurveConfig + Copy + Send> From<&Affine<P0>> for LeafValue<P0> {
    fn from(value: &Affine<P0>) -> Self {
        LeafValue(*value)
    }
}

impl<P0: SWCurveConfig + Copy + Send> From<Affine<P0>> for LeafValue<P0> {
    fn from(value: Affine<P0>) -> Self {
        LeafValue(value)
    }
}
