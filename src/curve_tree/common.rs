use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_serialize::{Compress, SerializationError, Valid, Validate};
use ark_std::Zero;
use codec::{Decode, Encode};
use curve_tree_relations::{
    curve_tree::SelRerandParameters, single_level_select_and_rerandomize::*,
};

use super::*;
use crate::error::*;

#[derive(Copy, Clone, Encode, Decode, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub enum NodeLocation<const L: usize> {
    Leaf(#[codec(compact)] LeafIndex), // Leaf nodes are identified by their index
    Odd {
        #[codec(compact)]
        level: NodeLevel, // Level of the node in the tree
        #[codec(compact)]
        index: NodeIndex, // Index of the node at that level
    },
    Even {
        #[codec(compact)]
        level: NodeLevel, // Level of the node in the tree
        #[codec(compact)]
        index: NodeIndex, // Index of the node at that level
    },
}

impl<const L: usize> NodeLocation<L> {
    /// Creates a leaf node location.
    pub fn leaf(leaf_index: LeafIndex) -> Self {
        // Leaf nodes are at level 0, and their index is the leaf_index
        Self::Leaf(leaf_index)
    }

    pub fn root(height: NodeLevel) -> Self {
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
    pub fn is_root(&self, height: NodeLevel) -> bool {
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
    pub fn level(&self) -> NodeLevel {
        match *self {
            Self::Leaf(_) => 0,
            Self::Odd { level, .. } | Self::Even { level, .. } => level,
        }
    }

    /// Returns the index of the node at its level.
    pub fn index(&self) -> NodeIndex {
        match *self {
            Self::Leaf(leaf_index) => leaf_index,
            Self::Odd { index, .. } | Self::Even { index, .. } => index,
        }
    }

    /// Returns the parent node location of this node.
    ///
    /// The parent is one level up, and its index is the integer division of the current index by L.
    pub fn parent(self) -> (Self, ChildIndex) {
        match self {
            Self::Leaf(leaf_index) => (
                Self::Odd {
                    level: 1,
                    index: leaf_index.saturating_div(L as LeafIndex),
                },
                leaf_index % L as LeafIndex,
            ),
            Self::Odd { level, index } => (
                Self::Even {
                    level: level.saturating_add(1),
                    index: index.saturating_div(L as NodeIndex),
                },
                index % L as NodeIndex,
            ),
            Self::Even { level, index } => (
                Self::Odd {
                    level: level.saturating_add(1),
                    index: index.saturating_div(L as NodeIndex),
                },
                index % L as NodeIndex,
            ),
        }
    }

    /// Returns the child node location of this node at the given child index.
    ///
    /// The child index must be less than L, and the child node is at one level down.
    /// The index of the child node is the current index multiplied by L plus the child index.
    pub fn child(self, child_index: ChildIndex) -> Result<Self, Error> {
        if child_index >= L as NodeIndex {
            return Err(Error::CurveTreeInvalidChildIndex(child_index));
        }
        match self {
            Self::Leaf(_) => {
                // Leaf nodes cannot have children, so we return an error.
                Err(Error::CurveTreeLeafCannotHaveChildren)
            }
            Self::Odd { level: 1, index } => Ok(Self::Leaf(index * L as LeafIndex + child_index)),
            Self::Odd { level, index } => Ok(Self::Even {
                level: level.saturating_sub(1),
                index: index * L as NodeIndex + child_index,
            }),
            Self::Even { level, index } => Ok(Self::Odd {
                level: level.saturating_sub(1),
                index: index * L as NodeIndex + child_index,
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
) -> Result<[Affine<P1>; M], Error> {
    let mut commitments = [Affine::<P1>::zero(); M];
    for tree_index in 0..M {
        let new_x_coord = (new_child.commitment(tree_index as TreeIndex) + delta)
            .into_affine()
            .x;
        let mut gen_iter = parameters
            .bp_gens
            .share(0)
            .G(L * (tree_index + 1))
            .skip(L * tree_index);
        let g = gen_iter.next().ok_or(Error::CurveTreeGeneratorNotFound)?;
        commitments[tree_index] =
            (commitments[tree_index].into_group() + *g * new_x_coord).into_affine();
    }
    Ok(commitments)
}

fn update_inner_node<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
>(
    commitments: &mut [Affine<P1>; M],
    local_index: ChildIndex,
    old_child: Option<ChildCommitments<M, P0>>,
    new_child: ChildCommitments<M, P0>,
    delta: &Affine<P0>,
    parameters: &SingleLayerParameters<P1>,
) -> Result<(), Error> {
    for tree_index in 0..M {
        let old_x_coord = if let Some(old_comm) = old_child {
            (old_comm.commitment(tree_index as TreeIndex) + delta)
                .into_affine()
                .x
        } else {
            P0::BaseField::zero()
        };
        let new_x_coord = (new_child.commitment(tree_index as TreeIndex) + delta)
            .into_affine()
            .x;
        let mut gen_iter = parameters
            .bp_gens
            .share(0)
            .G(L * (tree_index as usize + 1))
            .skip(L * tree_index as usize + local_index as usize);
        let g = gen_iter.next().ok_or(Error::CurveTreeGeneratorNotFound)?;
        commitments[tree_index] =
            (commitments[tree_index].into_group() + *g * (new_x_coord - old_x_coord)).into_affine();
    }
    Ok(())
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ChildCommitments<const M: usize, P0: SWCurveConfig> {
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

    pub fn commitment(&self, tree_index: TreeIndex) -> Affine<P0> {
        match self {
            ChildCommitments::Leaf(leaf) => leaf.0,
            ChildCommitments::Inner(commitments) => commitments[tree_index as usize],
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Inner<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    Even([Affine<P0>; M]),
    Odd([Affine<P1>; M]),
}

impl<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> CanonicalSerialize for Inner<M, P0, P1> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        match self {
            Inner::Even(commitments) => {
                0u8.serialize_with_mode(&mut writer, compress)?;
                commitments.serialize_with_mode(writer, compress)
            }
            Inner::Odd(commitments) => {
                1u8.serialize_with_mode(&mut writer, compress)?;
                commitments.serialize_with_mode(writer, compress)
            }
        }
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        match self {
            Inner::Even(commitments) => 1 + commitments.serialized_size(compress),
            Inner::Odd(commitments) => 1 + commitments.serialized_size(compress),
        }
    }
}

impl<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> Valid for Inner<M, P0, P1> {
    fn check(&self) -> Result<(), SerializationError> {
        match self {
            Inner::Even(commitments) => commitments.check(),
            Inner::Odd(commitments) => commitments.check(),
        }
    }
}

impl<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> CanonicalDeserialize
    for Inner<M, P0, P1>
{
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let t: u8 = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        match t {
            0 => {
                let commitments =
                    <[Affine<P0>; M]>::deserialize_with_mode(reader, compress, validate)?;
                Ok(Inner::Even(commitments))
            }
            1 => {
                let commitments =
                    <[Affine<P1>; M]>::deserialize_with_mode(reader, compress, validate)?;
                Ok(Inner::Odd(commitments))
            }
            _ => Err(SerializationError::InvalidData),
        }
    }
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
    pub(crate) fn init_empty_even<const L: usize>(
        new_child: ChildCommitments<M, P1>,
        delta: &Affine<P1>,
        parameters: &SingleLayerParameters<P0>,
    ) -> Result<Self, Error> {
        Ok(Self::Even(init_empty_inner_node::<L, M, P1, P0>(
            new_child, delta, parameters,
        )?))
    }

    pub(crate) fn init_empty_odd<const L: usize>(
        new_child: ChildCommitments<M, P0>,
        delta: &Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) -> Result<Self, Error> {
        Ok(Self::Odd(init_empty_inner_node::<L, M, P0, P1>(
            new_child, delta, parameters,
        )?))
    }

    pub(crate) fn update_even_node<const L: usize>(
        commitments: &mut [Affine<P0>; M],
        local_index: ChildIndex,
        old_child: Option<ChildCommitments<M, P1>>,
        new_child: ChildCommitments<M, P1>,
        delta: &Affine<P1>,
        parameters: &SingleLayerParameters<P0>,
    ) -> Result<(), Error> {
        update_inner_node::<L, M, P1, P0>(
            commitments,
            local_index,
            old_child,
            new_child,
            delta,
            parameters,
        )
    }

    pub(crate) fn update_odd_node<const L: usize>(
        commitments: &mut [Affine<P1>; M],
        local_index: ChildIndex,
        old_child: Option<ChildCommitments<M, P0>>,
        new_child: ChildCommitments<M, P0>,
        delta: &Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) -> Result<(), Error> {
        update_inner_node::<L, M, P0, P1>(
            commitments,
            local_index,
            old_child,
            new_child,
            delta,
            parameters,
        )
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
    height: NodeLevel,
    parameters: &'a SelRerandParameters<P0, P1>,
    location: NodeLocation<L>,
    child_index: ChildIndex,
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
        leaf_index: LeafIndex,
        old_leaf_value: Option<LeafValue<P0>>,
        new_leaf_value: LeafValue<P0>,
        height: NodeLevel,
        parameters: &'a SelRerandParameters<P0, P1>,
    ) -> Result<Self, Error> {
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

    pub fn is_new_height(&mut self) -> Option<NodeLevel> {
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

    pub fn move_to_parent(&mut self) -> Result<NodeLocation<L>, Error> {
        let (parent_location, child_index) = self.location.parent();
        self.location = parent_location;
        self.child_index = child_index;
        Ok(parent_location)
    }

    pub fn update_node(
        &mut self,
        node: Option<Inner<M, P0, P1>>,
    ) -> Result<Inner<M, P0, P1>, Error> {
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
                        )?;

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
                        )?;

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
                    )?
                } else {
                    // If the location is odd, we create an odd node.
                    Inner::init_empty_odd::<L>(
                        self.even_new_child,
                        &self.parameters.even_parameters.delta,
                        &self.parameters.odd_parameters,
                    )?
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

#[derive(Clone, Copy, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
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
