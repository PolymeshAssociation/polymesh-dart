use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_serialize::{Compress, Read, SerializationError, Valid, Validate, Write};
use ark_std::Zero;
use codec::{Decode, Encode};
use core::hash::Hasher;
use curve_tree_relations::single_level_select_and_rerandomize::*;
use scale_info::TypeInfo;

use super::*;
use crate::error::*;

/// Node position.
#[derive(Copy, Clone, Encode, Decode, TypeInfo, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodePosition {
    /// Level of the node in the tree.
    #[codec(compact)]
    pub level: NodeLevel,
    /// Index of the node at that level.
    #[codec(compact)]
    pub index: NodeIndex,
}

impl NodePosition {
    pub fn leaf(leaf_index: LeafIndex) -> Self {
        NodePosition {
            level: 0,
            index: leaf_index,
        }
    }

    pub fn root(height: NodeLevel) -> Self {
        NodePosition {
            level: height,
            index: 0,
        }
    }

    pub fn is_even(&self) -> bool {
        self.level % 2 == 0
    }

    pub fn is_leaf(&self) -> bool {
        self.level == 0
    }

    pub fn is_root(&self, height: NodeLevel) -> bool {
        self.level >= height && self.index == 0
    }

    pub fn parent<const L: usize>(&self) -> (NodePosition, ChildIndex) {
        (
            NodePosition {
                level: self.level.saturating_add(1),
                index: self.index.saturating_div(L as NodeIndex),
            },
            self.index % L as NodeIndex,
        )
    }

    pub fn child<const L: usize>(&self, child_index: ChildIndex) -> Result<NodePosition, Error> {
        if child_index >= L as NodeIndex {
            return Err(Error::CurveTreeInvalidChildIndex(child_index));
        }
        if self.level == 0 {
            return Err(Error::CurveTreeLeafCannotHaveChildren);
        }
        Ok(NodePosition {
            level: self.level.saturating_sub(1),
            index: self.index.saturating_mul(L as NodeIndex) + child_index,
        })
    }
}

/// Location of a node in the tree.
#[derive(Copy, Clone, Encode, Decode, TypeInfo, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeLocation<const L: usize> {
    Leaf(#[codec(compact)] LeafIndex), // Leaf nodes are identified by their index
    Odd(NodePosition),
    Even(NodePosition),
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
            Self::Even(NodePosition {
                level: height,
                index: 0,
            })
        } else {
            // Odd height, root is an odd node
            Self::Odd(NodePosition {
                level: height,
                index: 0,
            })
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
            Self::Odd(pos) | Self::Even(pos) => {
                // A node is a root if it is at the highest level and has index 0
                pos.is_root(height)
            }
        }
    }

    /// Returns the level of the node.
    ///
    /// Leaf nodes are at level 0, odd nodes are at their specified level, and even nodes are at their specified level.
    pub fn level(&self) -> NodeLevel {
        match *self {
            Self::Leaf(_) => 0,
            Self::Odd(pos) | Self::Even(pos) => pos.level,
        }
    }

    /// Returns the index of the node at its level.
    pub fn index(&self) -> NodeIndex {
        match *self {
            Self::Leaf(leaf_index) => leaf_index,
            Self::Odd(pos) | Self::Even(pos) => pos.index,
        }
    }

    /// Returns the parent node location of this node.
    ///
    /// The parent is one level up, and its index is the integer division of the current index by L.
    pub fn parent(self) -> (Self, ChildIndex) {
        match self {
            Self::Leaf(leaf_index) => (
                Self::Odd(NodePosition {
                    level: 1,
                    index: leaf_index.saturating_div(L as LeafIndex),
                }),
                leaf_index % L as LeafIndex,
            ),
            Self::Odd(pos) => {
                let (pos, child_index) = pos.parent::<L>();
                (Self::Even(pos), child_index)
            }
            Self::Even(pos) => {
                let (pos, child_index) = pos.parent::<L>();
                (Self::Odd(pos), child_index)
            }
        }
    }

    /// Get the position of the node to our left at the same level, if it exists.
    /// If this node is the leftmost node at its level, return None.
    /// Leaf nodes do not have siblings, so return None for them.
    ///
    /// This is used to help prune the left-side of a lean curve tree as we update it.
    /// When we insert a new node, we know that the left sibling (if it exists) will not change,
    /// so we can prune it from storage.
    pub fn left_sibling(self) -> Option<Self> {
        match self {
            Self::Leaf(_) => None, // Leaf nodes do not have siblings
            Self::Odd(pos) => {
                if pos.index == 0 {
                    None // Leftmost node, no left sibling
                } else {
                    Some(Self::Odd(NodePosition {
                        level: pos.level,
                        index: pos.index - 1,
                    }))
                }
            }
            Self::Even(pos) => {
                if pos.index == 0 {
                    None // Leftmost node, no left sibling
                } else {
                    Some(Self::Even(NodePosition {
                        level: pos.level,
                        index: pos.index - 1,
                    }))
                }
            }
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
            Self::Odd(NodePosition { level: 1, index }) => {
                Ok(Self::Leaf(index * L as LeafIndex + child_index))
            }
            Self::Odd(NodePosition { level, index }) => Ok(Self::Even(NodePosition {
                level: level.saturating_sub(1),
                index: index * L as NodeIndex + child_index,
            })),
            Self::Even(NodePosition { level, index }) => Ok(Self::Odd(NodePosition {
                level: level.saturating_sub(1),
                index: index * L as NodeIndex + child_index,
            })),
        }
    }
}

pub fn update_inner_node<
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
) -> Result<[P0::BaseField; M], Error> {
    let mut new_x_coords = [P0::BaseField::zero(); M];
    for (tree_index, new_x_coord) in new_x_coords.iter_mut().enumerate() {
        let old_x_coord = if let Some(old_comm) = old_child {
            (old_comm.commitment(tree_index as TreeIndex) + delta)
                .into_affine()
                .x
        } else {
            P0::BaseField::zero()
        };
        *new_x_coord = (new_child.commitment(tree_index as TreeIndex) + delta)
            .into_affine()
            .x;
        let mut gen_iter = parameters
            .bp_gens
            .share(0)
            .G(L * (tree_index as usize + 1))
            .skip(L * tree_index as usize + local_index as usize);
        let g = gen_iter.next().ok_or(Error::CurveTreeGeneratorNotFound)?;
        commitments[tree_index] = (commitments[tree_index].into_group()
            + *g * (*new_x_coord - old_x_coord))
            .into_affine();
    }
    Ok(new_x_coords)
}

#[derive(Clone, Encode, Decode)]
pub enum CompressedChildCommitments<const M: usize> {
    Leaf(CompressedAffine),
    Inner([CompressedAffine; M]),
}

impl<const M: usize> CompressedChildCommitments<M> {
    pub fn decompress<P0: SWCurveConfig + Copy + Send>(
        &self,
    ) -> Result<ChildCommitments<M, P0>, Error> {
        match self {
            CompressedChildCommitments::Leaf(ca) => {
                Ok(ChildCommitments::Leaf(LeafValue(ca.try_into()?)))
            }
            CompressedChildCommitments::Inner(cas) => {
                let mut as_ = [Affine::<P0>::zero(); M];
                for (i, ca) in cas.iter().enumerate() {
                    as_[i] = ca.try_into()?;
                }
                Ok(ChildCommitments::Inner(as_))
            }
        }
    }

    pub fn compress<P0: SWCurveConfig + Copy + Send>(
        child: ChildCommitments<M, P0>,
    ) -> Result<CompressedChildCommitments<M>, Error> {
        match child {
            ChildCommitments::Leaf(leaf) => {
                let ca = leaf.0.try_into()?;
                Ok(CompressedChildCommitments::Leaf(ca))
            }
            ChildCommitments::Inner(commitments) => {
                let mut cas = [CompressedAffine::default(); M];
                for (i, comm) in commitments.into_iter().enumerate() {
                    cas[i] = comm.try_into()?;
                }
                Ok(CompressedChildCommitments::Inner(cas))
            }
        }
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

    pub fn commitment(&self, tree_index: TreeIndex) -> Affine<P0> {
        match self {
            ChildCommitments::Leaf(leaf) => leaf.0,
            ChildCommitments::Inner(commitments) => commitments[tree_index as usize],
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Inner<const M: usize, C: CurveTreeConfig> {
    Even([Affine<C::P0>; M]),
    Odd([Affine<C::P1>; M]),
}

impl<const M: usize, C: CurveTreeConfig> CanonicalSerialize for Inner<M, C> {
    fn serialize_with_mode<W: Write>(
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

impl<const M: usize, C: CurveTreeConfig> Valid for Inner<M, C> {
    fn check(&self) -> Result<(), SerializationError> {
        match self {
            Inner::Even(commitments) => commitments.check(),
            Inner::Odd(commitments) => commitments.check(),
        }
    }
}

impl<const M: usize, C: CurveTreeConfig> CanonicalDeserialize for Inner<M, C> {
    fn deserialize_with_mode<R: Read>(
        mut reader: R,
        compress: Compress,
        validate: Validate,
    ) -> Result<Self, SerializationError> {
        let t: u8 = CanonicalDeserialize::deserialize_with_mode(&mut reader, compress, validate)?;
        match t {
            0 => {
                let commitments =
                    <[Affine<C::P0>; M]>::deserialize_with_mode(reader, compress, validate)?;
                Ok(Inner::Even(commitments))
            }
            1 => {
                let commitments =
                    <[Affine<C::P1>; M]>::deserialize_with_mode(reader, compress, validate)?;
                Ok(Inner::Odd(commitments))
            }
            _ => Err(SerializationError::InvalidData),
        }
    }
}

impl<const M: usize, C: CurveTreeConfig> core::fmt::Debug for Inner<M, C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Inner::Even(commitment) => write!(f, "Even({:?})", commitment),
            Inner::Odd(commitment) => write!(f, "Odd({:?})", commitment),
        }
    }
}

#[macro_export]
macro_rules! impl_curve_tree_with_backend {
    (Async, $curve_tree_ty:ident, $curve_tree_backend_trait:ident) => {
        impl_curve_tree_with_backend!(
            $curve_tree_ty,
            $curve_tree_backend_trait,
            { async },
            { .await }
        );
    };
    (Sync, $curve_tree_ty:ident, $curve_tree_backend_trait:ident) => {
        impl_curve_tree_with_backend!(
            $curve_tree_ty,
            $curve_tree_backend_trait,
            { }, { }
        );

        impl<
            const L: usize,
            const M: usize,
            C: CurveTreeConfig,
            B: $curve_tree_backend_trait<L, M, C, Error = Error>,
            Error: From<crate::Error>,
        > CurveTreeLookup<L, M, C> for &$curve_tree_ty<L, M, C, B, Error>
        {
            fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, error::Error> {
                Ok($curve_tree_ty::get_path_to_leaf(self,leaf_index, 0).map_err(|_| error::Error::LeafIndexNotFound(leaf_index))?)
            }

            fn get_path_to_leaf(
                &self,
                _leaf: LeafValue<C::P0>,
            ) -> Result<CurveTreePath<L, C>, error::Error> {
                Err(error::Error::LeafNotFound)
            }

            fn params(&self) -> &CurveTreeParameters<C> {
                self.parameters()
            }

            fn root_node(&self) -> Result<CurveTreeRoot<L, M, C>, error::Error> {
                let root = $curve_tree_ty::root_node(self).map_err(|_| error::Error::CurveTreeRootNotFound)?;
                Ok(CurveTreeRoot::new(&root)?)
            }

            fn get_block_number(&self) -> Result<BlockNumber, error::Error> {
                Ok($curve_tree_ty::get_block_number(self).map_err(|_| error::Error::CurveTreeBlockNumberNotFound)?)
            }
        }

        impl<
            const L: usize,
            const M: usize,
            C: CurveTreeConfig,
            B: $curve_tree_backend_trait<L, M, C, Error = Error>,
            Error: From<crate::Error>,
        > ValidateCurveTreeRoot<L, M, C> for &$curve_tree_ty<L, M, C, B, Error>
        {
            fn get_block_root(&self, block: BlockNumber) -> Option<CurveTreeRoot<L, M, C>> {
                let root = self.fetch_root(block).ok()?;
                CurveTreeRoot::new(&root).ok()
            }

            fn params(&self) -> &CurveTreeParameters<C> {
                self.parameters()
            }
        }
    };
    ($curve_tree_ty:ident, $curve_tree_backend_trait:ident, { $($async_fn:tt)* }, { $($await:tt)* }) => {
        pub struct $curve_tree_ty<
            const L: usize,
            const M: usize,
            C: CurveTreeConfig,
            B: $curve_tree_backend_trait<L, M, C, Error = Error> = CurveTreeMemoryBackend<L, M, C>,
            Error: From<crate::Error> = crate::Error,
        > {
            pub backend: B,
            _marker: core::marker::PhantomData<C>,
        }

        impl<
            const L: usize,
            const M: usize,
            C: CurveTreeConfig,
            B: Clone + $curve_tree_backend_trait<L, M, C, Error = Error>,
            Error: From<crate::Error>,
        > Clone for $curve_tree_ty<L, M, C, B, Error>
        {
            fn clone(&self) -> Self {
                Self {
                    backend: self.backend.clone(),
                    _marker: core::marker::PhantomData,
                }
            }
        }
        impl<
            const L: usize,
            const M: usize,
            C: CurveTreeConfig,
            B: $curve_tree_backend_trait<L, M, C, Error = Error>,
            Error: From<crate::Error>,
        > $curve_tree_ty<L, M, C, B, Error>
        {
            pub $($async_fn)* fn new(
                height: NodeLevel,
                gens_length: usize,
            ) -> Result<Self, Error> {
                let mut tree = Self::new_no_init(height, gens_length)$($await)*?;
                tree.init_root()$($await)*?;
                Ok(tree)
            }

            pub $($async_fn)* fn new_no_init(
                height: NodeLevel,
                gens_length: usize,
            ) -> Result<Self, Error> {
                let backend = B::new(height, gens_length)$($await)*?;
                Ok(Self::new_with_backend(backend)$($await)*?)
            }

            pub $($async_fn)* fn new_with_backend(
                backend: B,
            ) -> Result<Self, Error> {
                Ok(Self {
                    backend,
                    _marker: core::marker::PhantomData,
                })
            }
        }

        impl<
            const L: usize,
            const M: usize,
            C: CurveTreeConfig,
            B: $curve_tree_backend_trait<L, M, C, Error = Error>,
            Error: From<crate::Error>,
        > $curve_tree_ty<L, M, C, B, Error>
        {
            /// Initializes the root of the tree by setting the first leaf to the default value.
            pub $($async_fn)* fn init_root(&mut self) -> Result<(), Error> {
                // Check if the root node has already been initialized.
                let root = self.root_node()$($await)*;
                if root.is_err() {
                    // No root node exists, so we need to initialize the tree.
                    self.init_inner_nodes()$($await)*?;
                }
                Ok(())
            }

            $($async_fn)* fn init_inner_nodes(
                &mut self,
            ) -> Result<(), Error> {
                let height = self.height()$($await)*;

                // Start at the first leaf's location.
                let mut location = NodeLocation::<L>::leaf(0);
                // Move to the first inner node location above the leaves.
                let (parent_location, _) = location.parent();
                location = parent_location;
                // Initialize the first inner node as an odd node with zero commitments.
                let commitments = [Affine::<C::P1>::zero(); M];
                let node = Inner::Odd(commitments.clone());
                self.backend.set_inner_node(location, node)$($await)*?;

                let mut updater = B::updater();

                // Keep going until we reach the root of the tree.
                while !location.is_root(height) {
                    // Move to the parent location and get the child index of the current node.
                    let (parent_location, child_index) = location.parent();
                    location = parent_location;

                    // If thsi node does not exist, we need to create it.
                    let node = if location.is_even() {
                        let mut commitments = [Affine::<C::P0>::zero(); M];
                        updater.update_even_node(
                            &mut commitments,
                            child_index,
                            None,
                            None,
                        )?;
                        Inner::Even(commitments)
                    } else {
                        let mut commitments = [Affine::<C::P1>::zero(); M];
                        updater.update_odd_node(
                            &mut commitments,
                            child_index,
                            None,
                            None,
                        )?;
                        Inner::Odd(commitments)
                    };

                    // Save the updated node back to the backend.
                    self.backend.set_inner_node(location, node)$($await)*?;
                }
                Ok(())
            }

            pub $($async_fn)* fn height(&self) -> NodeLevel {
                self.backend.height()$($await)*
            }

            pub $($async_fn)* fn parameters(&self) -> &SelRerandParameters<C::P0, C::P1> {
                self.backend.parameters()$($await)*
            }

            pub $($async_fn)* fn insert_leaf(
                &mut self,
                leaf_value: LeafValue<C::P0>,
            ) -> Result<LeafIndex, Error> {
                // Make sure there are no uncommitted leaves.
                self.commit_leaves_to_tree()$($await)*?;

                // Insert the leaf.
                let leaf_index = self.insert_leaf_delayed_update(leaf_value)$($await)*?;

                // Now update the tree with the new leaf.
                self.update_tree(leaf_index, None, leaf_value)$($await)*?;

                // If the backend supports batch inserts, we need to mark this leaf as committed.
                if self.backend.batch_inserts_supported() {
                    // Mark this leaf as committed.
                    self.backend.set_committed_leaf_index(leaf_index + 1)$($await)*?;
                }
                Ok(leaf_index)
            }

            pub $($async_fn)* fn insert_leaf_delayed_update(
                &mut self,
                leaf_value: LeafValue<C::P0>,
            ) -> Result<LeafIndex, Error> {
                let leaf_index = self.backend.allocate_leaf_index()$($await)*;
                self.backend.set_leaf(leaf_index, leaf_value)$($await)*?;
                Ok(leaf_index)
            }

            pub $($async_fn)* fn get_leaf(&self, leaf_index: LeafIndex) -> Result<Option<LeafValue<C::P0>>, Error> {
                self.backend.get_leaf(leaf_index)$($await)*
            }

            $($async_fn)* fn _get_odd_x_coord_children_batch(
                &self,
                parent: NodeLocation<L>,
                delta: &Affine<C::P1>,
            ) -> Result<Vec<[<C::P1 as ark_ec::CurveConfig>::BaseField; L]>, Error> {
                let mut batch_x_coord_children = Vec::with_capacity(M);
                for tree_index in 0..M {
                    let x_coord_children = self
                        ._get_odd_x_coord_children(tree_index as TreeIndex, parent, delta)
                        $($await)*?;
                    batch_x_coord_children.push(x_coord_children);
                }
                Ok(batch_x_coord_children)
            }

            $($async_fn)* fn _get_odd_x_coord_children(
                &self,
                tree_index: TreeIndex,
                parent: NodeLocation<L>,
                delta: &Affine<C::P1>,
            ) -> Result<[<C::P1 as ark_ec::CurveConfig>::BaseField; L], Error> {
                let mut x_coord_children = [<C::P1 as ark_ec::CurveConfig>::BaseField::zero(); L];
                for idx in 0..L {
                    let child = parent.child(idx as ChildIndex)?;
                    let x_coord = match self.backend.get_inner_node(child)$($await)*? {
                        Some(Inner::Odd(commitments)) => {
                            Some((commitments[tree_index as usize] + delta).into_affine().x)
                        }
                        Some(Inner::Even(_)) => {
                            return Err(crate::Error::CurveTreeInvalidChildNode {
                                level: child.level(),
                                index: child.index(),
                            }.into());
                        }
                        None => None,
                    };
                    if let Some(x_coord) = x_coord {
                        x_coord_children[idx] = x_coord;
                    }
                }
                Ok(x_coord_children)
            }

            $($async_fn)* fn _get_even_x_coord_children_batch(
                &self,
                parent: NodeLocation<L>,
                delta: &Affine<C::P0>,
            ) -> Result<Vec<[<C::P0 as ark_ec::CurveConfig>::BaseField; L]>, Error> {
                let mut batch_x_coord_children = Vec::with_capacity(M);
                for tree_index in 0..M {
                    let x_coord_children = self
                        ._get_even_x_coord_children(tree_index as TreeIndex, parent, delta)
                        $($await)*?;
                    batch_x_coord_children.push(x_coord_children);
                }
                Ok(batch_x_coord_children)
            }

            $($async_fn)* fn _get_even_x_coord_children(
                &self,
                tree_index: TreeIndex,
                parent: NodeLocation<L>,
                delta: &Affine<C::P0>,
            ) -> Result<[<C::P0 as ark_ec::CurveConfig>::BaseField; L], Error> {
                let mut x_coord_children = [<C::P0 as ark_ec::CurveConfig>::BaseField::zero(); L];
                for idx in 0..L {
                    let child = parent.child(idx as ChildIndex)?;
                    let commitment = if let NodeLocation::Leaf(leaf_index) = child {
                        self.backend.get_leaf(leaf_index)$($await)*?.map(|leaf| leaf.0)
                    } else {
                        match self.backend.get_inner_node(child)$($await)*? {
                            Some(Inner::Even(commitments)) => Some(commitments[tree_index as usize]),
                            Some(Inner::Odd(_)) => {
                                log::error!("An Odd node cannot have an odd child");
                                return Err(crate::Error::CurveTreeInvalidChildNode {
                                    level: child.level(),
                                    index: child.index(),
                                }.into());
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

            pub $($async_fn)* fn root_node(
                &self,
            ) -> Result<Root<L, M, C::P0, C::P1>, Error> {
                let params = self.parameters()$($await)*;
                let root = NodeLocation::<L>::root(self.height()$($await)*);
                match self.backend.get_inner_node(root)$($await)*? {
                    Some(Inner::Even(commitments)) => Ok(Root::Even(RootNode {
                        commitments: commitments.clone(),
                        x_coord_children: self
                            ._get_odd_x_coord_children_batch(root, &params.odd_parameters.delta)
                            $($await)*?,
                    })),
                    Some(Inner::Odd(commitments)) => Ok(Root::Odd(RootNode {
                        commitments: commitments.clone(),
                        x_coord_children: self
                            ._get_even_x_coord_children_batch(root, &params.even_parameters.delta)
                            $($await)*?,
                    })),
                    None => Err(crate::Error::CurveTreeRootNotFound.into()),
                }
            }

            pub $($async_fn)* fn get_block_number(&self) -> Result<BlockNumber, Error> {
                let block_number = self.backend.get_block_number()$($await)*?;
                Ok(block_number)
            }

            pub $($async_fn)* fn set_block_number(&mut self, block_number: BlockNumber) -> Result<(), Error> {
                self.backend.set_block_number(block_number)$($await)*?;
                Ok(())
            }

            pub $($async_fn)* fn store_root(&mut self) -> Result<BlockNumber, Error> {
                let root = self.root_node()$($await)*?;
                let block_number = self.backend.store_root(root)$($await)*?;
                Ok(block_number)
            }

            pub $($async_fn)* fn fetch_root(&self, block_number: BlockNumber) -> Result<Root<L, M, C::P0, C::P1>, Error> {
                self.backend.fetch_root(block_number)$($await)*.map_err(|_| crate::Error::CurveTreeRootNotFound.into())
            }

            pub $($async_fn)* fn get_path_to_leaf(
                &self,
                leaf_index: LeafIndex,
                tree_index: TreeIndex,
            ) -> Result<CurveTreeWitnessPath<L, C::P0, C::P1>, Error> {
                let height = self.height()$($await)*;
                let mut even_internal_nodes = Vec::with_capacity(height as usize);
                let mut odd_internal_nodes = Vec::with_capacity(height as usize);

                let mut even_child = self
                    .backend
                    .get_leaf(leaf_index)
                    $($await)*?
                    .map(|leaf| leaf.0)
                    .ok_or_else(|| crate::Error::CurveTreeLeafIndexOutOfBounds(leaf_index).into())?;
                let mut odd_child = Affine::<C::P1>::zero();

                // Start at the leaf's location.
                let mut location = NodeLocation::<L>::leaf(leaf_index);

                // Get the parameters for the tree.
                let params = self.parameters()$($await)*;

                while !location.is_root(height) {
                    let (parent_location, _) = location.parent();
                    let node = self
                        .backend
                        .get_inner_node(parent_location)
                        $($await)*?
                        .ok_or_else(|| crate::Error::CurveTreeNodeNotFound {
                            level: parent_location.level(),
                            index: parent_location.index(),
                        }.into())?;

                    match node {
                        Inner::Even(commitments) => {
                            even_child = commitments[tree_index as usize];
                            even_internal_nodes.push(WitnessNode {
                                x_coord_children: self
                                    ._get_odd_x_coord_children(
                                        tree_index,
                                        parent_location,
                                        &params.odd_parameters.delta,
                                    )
                                    $($await)*?,
                                child_node_to_randomize: odd_child,
                            });
                        }
                        Inner::Odd(commitments) => {
                            odd_child = commitments[tree_index as usize];
                            odd_internal_nodes.push(WitnessNode {
                                x_coord_children: self
                                    ._get_even_x_coord_children(
                                        tree_index,
                                        parent_location,
                                        &params.even_parameters.delta,
                                    )
                                    $($await)*?,
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

            pub $($async_fn)* fn update_leaf(
                &mut self,
                leaf_index: LeafIndex,
                new_leaf_value: LeafValue<C::P0>,
            ) -> Result<(), Error> {
                // Make sure there are no uncommitted leaves.
                self.commit_leaves_to_tree()$($await)*?;

                // Update the leaf to the new value and get the old value.
                let old_leaf_value = self.backend.set_leaf(leaf_index, new_leaf_value)$($await)*?;
                if C::APPEND_ONLY {
                    if old_leaf_value.is_some() {
                        return Err(crate::Error::CurveTreeCannotUpdateLeafInAppendOnlyTree.into());
                    }
                }

                self.update_tree(leaf_index, old_leaf_value, new_leaf_value)$($await)*
            }

            pub $($async_fn)* fn commit_leaves_to_tree(
                &mut self,
            ) -> Result<bool, Error> {
                if !self.backend.batch_inserts_supported() {
                    // This tree doesn't support delayed commiting.
                    return Ok(false);
                }
                let mut leaf_index = self.backend.last_committed_leaf_index()$($await)*?;
                let leaf_count = self.backend.leaf_count()$($await)*;
                let pending_leaves = leaf_count.saturating_sub(leaf_index);
                if pending_leaves == 0 {
                    // No new leaves to commit.
                    return Ok(false);
                }

                let mut height = self.height()$($await)*;

                let mut updater = B::updater();

                while leaf_index < leaf_count {
                    let leaf_value = self
                        .backend
                        .get_leaf(leaf_index)
                        $($await)*?
                        .ok_or_else(|| crate::Error::CurveTreeLeafIndexOutOfBounds(leaf_index).into())?;

                    updater.next_leaf(None, leaf_value);

                    // Start at the leaf's location.
                    let mut location = NodeLocation::<L>::leaf(leaf_index);
                    let mut child_is_leaf = true;

                    leaf_index += 1;
                    // Keep going until we reach the root of the tree.
                    while !location.is_root(height) {
                        // Move to the parent location and get the child index of the current node.
                        let (parent_location, mut child_index) = location.parent();
                        location = parent_location;

                        // Get or initialize the node at this location.
                        let mut is_new_node = false;
                        let mut node = self.backend.get_inner_node(location)$($await)*?.unwrap_or_else(|| {
                            is_new_node = true;
                            if location.is_even() {
                                // Create a new even node with zero commitments.
                                Inner::Even([Affine::<C::P0>::zero(); M])
                            } else {
                                // Create a new odd node with zero commitments.
                                Inner::Odd([Affine::<C::P1>::zero(); M])
                            }
                        });

                        match &mut node {
                            Inner::Even(commitments) => {
                                updater.update_even_node(
                                    commitments,
                                    child_index,
                                    Some(is_new_node),
                                    None,
                                )?;
                            }
                            Inner::Odd(commitments) => {
                                updater.update_odd_node(
                                    commitments,
                                    child_index,
                                    Some(is_new_node),
                                    None,
                                )?;

                                // If the child was a leaf, we may need to commit multiple leaves to this node.
                                if child_is_leaf {
                                    // Try to commit as many leaves as possible to this node.
                                    while child_index < L as ChildIndex - 1 && leaf_index < leaf_count {
                                        // Commit the next child leaf.
                                        child_index += 1;
                                        // Get the next uncommitted leaf.
                                        let leaf_value = self
                                            .backend
                                            .get_leaf(leaf_index)
                                            $($await)*?
                                            .ok_or_else(|| crate::Error::CurveTreeLeafIndexOutOfBounds(leaf_index).into())?;
                                        updater.next_leaf(None, leaf_value);
                                        leaf_index += 1;

                                        updater.update_odd_node(
                                            commitments,
                                            child_index,
                                            None,
                                            None,
                                        )?;
                                    }
                                }

                                // Save the new commitment value for updating the parent.
                                child_is_leaf = false;
                            }
                        }

                        // Save the updated node back to the backend.
                        self.backend.set_inner_node(location, node)$($await)*?;
                    }

                    // Check if the tree has grown to accommodate the new leaf.
                    // if the root's level is higher than the current height, we need to update the height.
                    let level = location.level();
                    if level > height {
                        log::warn!("Tree height increased from {} to {}", height, level);
                        self.backend.set_height(level)$($await)*?;
                        height = level;
                    }
                }
                // Update the last committed leaf index in the backend.
                self.backend.set_committed_leaf_index(leaf_index)$($await)*?;

                Ok(true)
            }

            $($async_fn)* fn update_tree(
                &mut self,
                leaf_index: LeafIndex,
                old_leaf_value: Option<LeafValue<C::P0>>,
                new_leaf_value: LeafValue<C::P0>,
            ) -> Result<(), Error> {
                let height = self.height()$($await)*;

                let mut updater = B::updater();
                updater.next_leaf(old_leaf_value, new_leaf_value);

                // Start at the leaf's location.
                let mut location = NodeLocation::<L>::leaf(leaf_index);

                // Keep going until we reach the root of the tree.
                while !location.is_root(height) {
                    // Move to the parent location and get the child index of the current node.
                    let (parent_location, child_index) = location.parent();
                    location = parent_location;

                    let mut is_new_node = false;
                    let mut node = self.backend.get_inner_node(location)$($await)*?.unwrap_or_else(|| {
                        is_new_node = true;
                        if location.is_even() {
                            // Create a new even node with zero commitments.
                            Inner::Even([Affine::<C::P0>::zero(); M])
                        } else {
                            // Create a new odd node with zero commitments.
                            Inner::Odd([Affine::<C::P1>::zero(); M])
                        }
                    });
                    match &mut node {
                        Inner::Even(commitments) => {
                            updater.update_even_node(
                                commitments,
                                child_index,
                                Some(is_new_node),
                                None,
                            )?;
                        }
                        Inner::Odd(commitments) => {
                            updater.update_odd_node(
                                commitments,
                                child_index,
                                Some(is_new_node),
                                None,
                            )?;
                        }
                    }

                    // Save the updated node back to the backend.
                    self.backend.set_inner_node(location, node)$($await)*?;
                }

                // Check if the tree has grown to accommodate the new leaf.
                // if the root's level is higher than the current height, we need to update the height.
                let level = location.level();
                if level > height {
                    log::warn!("Tree height increased from {} to {}", height, level);
                    self.backend.set_height(level)$($await)*?;
                }
                Ok(())
            }
        }

        impl<
            const L: usize,
            const M: usize,
            C: CurveTreeConfig,
            B: $curve_tree_backend_trait<L, M, C, Error = Error>,
            Error: From<crate::Error>,
        > $curve_tree_ty<L, M, C, B, Error>
        {
            pub $($async_fn)* fn get_path_and_root(
                &self,
                leaf_index: LeafIndex,
            ) -> Result<LeafPathAndRoot<L, M, C>, Error> {
                // Get the leaf and path for the given leaf index.
                let leaf = self
                    .backend
                    .get_leaf(leaf_index)
                    $($await)*?
                    .ok_or_else(|| crate::Error::LeafIndexNotFound(leaf_index))?;
                let path = self.get_path_to_leaf(leaf_index, 0)$($await)*?;
                let block_number = self.get_block_number()$($await)*?;
                let root = self.root_node()$($await)*?;
                Ok(LeafPathAndRoot {
                    leaf: leaf.0.try_into()?,
                    leaf_index,
                    path: WrappedCanonical::wrap(&path)?,
                    block_number,
                    root: CurveTreeRoot::new(&root)?,
                })
            }
        }
    };
}

#[derive(Clone, Copy, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq)]
pub struct LeafValue<P0: SWCurveConfig>(pub(crate) Affine<P0>);

impl<P0: SWCurveConfig> LeafValue<P0> {
    pub fn as_compressed_affline(&self) -> Result<CompressedAffine, Error> {
        self.0.try_into()
    }
}

impl<P0: SWCurveConfig + Copy + Send> core::ops::Deref for LeafValue<P0> {
    type Target = Affine<P0>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<P0: SWCurveConfig + Copy + Send> core::hash::Hash for LeafValue<P0> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<P0: SWCurveConfig + Copy + Send> Default for LeafValue<P0> {
    fn default() -> Self {
        Self(Affine::<P0>::zero())
    }
}

impl<P0: SWCurveConfig + Copy + Send> core::fmt::Debug for LeafValue<P0> {
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
