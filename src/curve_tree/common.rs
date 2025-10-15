#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use codec::{Decode, Encode};
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
    child_index: ChildIndex,
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
            .G((L * (tree_index + 1)) as u32)
            .skip(L * tree_index + child_index as usize);
        let g = gen_iter.next().ok_or(Error::CurveTreeGeneratorNotFound)?;
        commitments[tree_index] = (commitments[tree_index].into_group()
            + *g * (*new_x_coord - old_x_coord))
            .into_affine();
    }
    Ok(new_x_coords)
}

#[derive(Copy, Clone, Encode, Decode)]
pub enum CompressedChildCommitments<const M: usize> {
    Leaf(CompressedAffine),
    Inner([CompressedAffine; M]),
}

impl<const M: usize> CompressedChildCommitments<M> {
    pub fn leaf<C: CurveTreeConfig>(leaf: CompressedLeafValue<C>) -> Self {
        Self::Leaf(leaf.into())
    }

    pub fn zero<P0: SWCurveConfig>() -> Self {
        Self::Leaf(CompressedAffine::zero::<P0>())
    }

    pub fn decompress<P0: SWCurveConfig + Copy + Send>(
        &self,
    ) -> Result<ChildCommitments<M, P0>, Error> {
        match self {
            CompressedChildCommitments::Leaf(ca) => Ok(ChildCommitments::Leaf(ca.try_into()?)),
            CompressedChildCommitments::Inner(cas) => {
                let mut as_ = [Affine::<P0>::zero(); M];
                for (i, ca) in cas.iter().enumerate() {
                    as_[i] = ca.try_into()?;
                }
                Ok(ChildCommitments::Inner(as_))
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum ChildCommitments<const M: usize, P0: SWCurveConfig> {
    Leaf(Affine<P0>),
    Inner([Affine<P0>; M]),
}

impl<const M: usize, P0: SWCurveConfig + Copy + Send> ChildCommitments<M, P0> {
    pub fn commitment(&self, tree_index: TreeIndex) -> Affine<P0> {
        match self {
            ChildCommitments::Leaf(leaf) => *leaf,
            ChildCommitments::Inner(commitments) => commitments[tree_index as usize],
        }
    }
}

#[derive(Clone, Encode, Decode, TypeInfo, Debug)]
pub struct CompressedXCoords<const M: usize> {
    pub x_coords: [CompressedBaseField; M],
}

impl<const M: usize> Default for CompressedXCoords<M> {
    fn default() -> Self {
        Self {
            x_coords: [CompressedBaseField::default(); M],
        }
    }
}

impl<const M: usize> CompressedXCoords<M> {
    pub fn default() -> Self {
        Self {
            x_coords: [CompressedBaseField::default(); M],
        }
    }

    pub fn decompress<P0: SWCurveConfig + Copy + Send>(&self) -> Result<[P0::BaseField; M], Error> {
        let mut x_coords = [P0::BaseField::zero(); M];
        for (i, cbf) in self.x_coords.iter().enumerate() {
            x_coords[i] = cbf.to_base_field()?;
        }
        Ok(x_coords)
    }

    pub fn compress<P0: SWCurveConfig + Copy + Send>(
        x_coords: &[P0::BaseField; M],
    ) -> Result<Self, Error> {
        let mut cbfs = [CompressedBaseField::default(); M];
        for (i, x) in x_coords.iter().enumerate() {
            cbfs[i] = CompressedBaseField::from_base_field(x)?;
        }
        Ok(Self { x_coords: cbfs })
    }
}

#[derive(Clone, Encode, Decode, TypeInfo, Debug)]
#[scale_info(skip_type_params(C))]
pub struct CompressedInner<const M: usize, C: CurveTreeConfig> {
    pub is_even: bool,
    pub commitments: [CompressedAffine; M],
    #[codec(skip)]
    _marker: PhantomData<C>,
}

impl<const M: usize, C: CurveTreeConfig> CompressedInner<M, C> {
    pub fn default_odd() -> Self {
        Self {
            is_even: false,
            commitments: [CompressedAffine::zero::<C::P1>(); M],
            _marker: PhantomData,
        }
    }

    pub fn default_even() -> Self {
        Self {
            is_even: true,
            commitments: [CompressedAffine::zero::<C::P0>(); M],
            _marker: PhantomData,
        }
    }

    pub fn compress(inner: &Inner<M, C>) -> Result<Self, Error> {
        match inner {
            Inner::Even(commitments) => {
                let mut cas = [CompressedAffine::default(); M];
                for (i, comm) in commitments.iter().enumerate() {
                    cas[i] = (*comm).try_into()?;
                }
                Ok(CompressedInner {
                    is_even: true,
                    commitments: cas,
                    _marker: PhantomData,
                })
            }
            Inner::Odd(commitments) => {
                let mut cas = [CompressedAffine::default(); M];
                for (i, comm) in commitments.iter().enumerate() {
                    cas[i] = (*comm).try_into()?;
                }
                Ok(CompressedInner {
                    is_even: false,
                    commitments: cas,
                    _marker: PhantomData,
                })
            }
        }
    }

    pub fn decompress(&self) -> Result<Inner<M, C>, Error> {
        if self.is_even {
            let mut as_ = [Affine::<C::P0>::zero(); M];
            for (i, ca) in self.commitments.iter().enumerate() {
                as_[i] = ca.try_into()?;
            }
            Ok(Inner::Even(as_))
        } else {
            let mut as_ = [Affine::<C::P1>::zero(); M];
            for (i, ca) in self.commitments.iter().enumerate() {
                as_[i] = ca.try_into()?;
            }
            Ok(Inner::Odd(as_))
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Inner<const M: usize, C: CurveTreeConfig> {
    Even([Affine<C::P0>; M]),
    Odd([Affine<C::P1>; M]),
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
                Ok($curve_tree_ty::get_path_to_leaf(self,leaf_index, 0, None).map_err(|_| error::Error::LeafIndexNotFound(leaf_index))?)
            }

            fn get_path_to_leaf(
                &self,
                _leaf: CompressedLeafValue<C>,
            ) -> Result<CurveTreePath<L, C>, error::Error> {
                Err(error::Error::LeafNotFound)
            }

            fn params(&self) -> &CurveTreeParameters<C> {
                C::parameters()
            }

            fn root(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, error::Error> {
                $curve_tree_ty::<L, M, C, B, Error>::root(self).map_err(|_| error::Error::CurveTreeRootNotFound)
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
            fn get_block_root(&self, block: BlockNumber) -> Option<CompressedCurveTreeRoot<L, M, C>> {
                self.fetch_root(Some(block)).ok()
            }

            fn params(&self) -> &CurveTreeParameters<C> {
                C::parameters()
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
            ) -> Result<Self, Error> {
                let mut tree = Self::new_no_init(height)$($await)*?;
                tree.init_root()$($await)*?;
                Ok(tree)
            }

            pub $($async_fn)* fn new_no_init(
                height: NodeLevel,
            ) -> Result<Self, Error> {
                let backend = B::new(height)$($await)*?;
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
                self.get_or_init_root()$($await)*?;
                Ok(())
            }

            /// Get or initialize the tree root.
            $($async_fn)* fn get_or_init_root(&mut self) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
                // Check if the root has already been initialized.
                if let Ok(root) = self.backend.current_root()$($await)* {
                    Ok(root)
                } else {
                    // No root node exists, so we need to initialize the tree.
                    let root = self.init_inner_nodes()$($await)*?;

                    // Store the root in the backend.
                    self.backend.store_root(root.clone())$($await)*?;

                    Ok(root)
                }
            }

            $($async_fn)* fn init_inner_nodes(
                &mut self,
            ) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
                let height = self.height()$($await)*;
                let mut current_root = CompressedCurveTreeRoot::new(height);

                // Start at the first leaf's location.
                let mut location = NodeLocation::<L>::leaf(0);
                // Move to the first inner node location above the leaves.
                let (parent_location, _) = location.parent();
                location = parent_location;
                let mut is_root = location.is_root(height);

                // Initialize the first inner node as an odd node with zero commitments.
                let node = CompressedInner::default_odd();
                // Update the root
                if is_root {
                    current_root.compressed_update(node.commitments, CompressedXCoords::default(), 0)?;
                }
                self.backend.set_inner_node(location, node)$($await)*?;

                let mut even_new_child = CompressedChildCommitments::zero::<C::P0>();
                let mut odd_new_child = CompressedChildCommitments::zero::<C::P1>();

                // Keep going until we reach the root of the tree.
                while !is_root {
                    // Move to the parent location and get the child index of the current node.
                    let (parent_location, child_index) = location.parent();
                    location = parent_location;
                    is_root = location.is_root(height);

                    // If thsi node does not exist, we need to create it.
                    let (node, new_x_coords) = if location.is_even() {
                        let mut inner = CompressedInner::default_even();
                        let new_x_coords = B::Updater::update_node(
                            &mut inner,
                            child_index,
                            None,
                            odd_new_child,
                        )?;

                        even_new_child = CompressedChildCommitments::Inner(inner.commitments);

                        (inner, new_x_coords)
                    } else {
                        let mut inner = CompressedInner::default_odd();
                        let new_x_coords = B::Updater::update_node(
                            &mut inner,
                            child_index,
                            None,
                            even_new_child,
                        )?;

                        odd_new_child = CompressedChildCommitments::Inner(inner.commitments);

                        (inner, new_x_coords)
                    };

                    // Update the root
                    if is_root {
                        current_root.compressed_update(node.commitments, new_x_coords, child_index)?;
                    }

                    // Save the updated node back to the backend.
                    self.backend.set_inner_node(location, node)$($await)*?;
                }
                Ok(current_root)
            }

            pub $($async_fn)* fn height(&self) -> NodeLevel {
                self.backend.height()$($await)*
            }

            pub fn parameters(&self) -> &SelRerandParameters<C::P0, C::P1> {
                C::parameters()
            }

            pub $($async_fn)* fn insert_leaf(
                &mut self,
                leaf_value: CompressedLeafValue<C>,
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
                leaf_value: CompressedLeafValue<C>,
            ) -> Result<LeafIndex, Error> {
                let leaf_index = self.backend.allocate_leaf_index()$($await)*;
                self.backend.set_leaf(leaf_index, leaf_value)$($await)*?;
                Ok(leaf_index)
            }

            pub $($async_fn)* fn get_leaf(&self, leaf_index: LeafIndex, block_number: Option<BlockNumber>) -> Result<Option<CompressedLeafValue<C>>, Error> {
                self.backend.get_leaf(leaf_index, block_number)$($await)*
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
                    let x_coord = match self.backend.get_inner_node(child, None)$($await)*? {
                        Some(node) => match node.decompress()? {
                            Inner::Odd(commitments) => {
                                Some((commitments[tree_index as usize] + delta).into_affine().x)
                            }
                            Inner::Even(_) => {
                                return Err(crate::Error::CurveTreeInvalidChildNode {
                                    level: child.level(),
                                    index: child.index(),
                                }.into());
                            }
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
                        self.backend.get_leaf(leaf_index, None)$($await)*?.and_then(|leaf| leaf.decompress().ok())
                    } else {
                        match self.backend.get_inner_node(child, None)$($await)*? {
                            Some(node) => match node.decompress()? {
                                Inner::Even(commitments) => Some(commitments[tree_index as usize]),
                                Inner::Odd(_) => {
                                    log::error!("An Odd node cannot have an odd child");
                                    return Err(crate::Error::CurveTreeInvalidChildNode {
                                        level: child.level(),
                                        index: child.index(),
                                    }.into());
                                }
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

            pub $($async_fn)* fn root(
                &self,
            ) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
                if let Ok(root) = self.backend.current_root()$($await)* {
                    Ok(root)
                } else {
                    // Fallback to slow build if not found in storage.
                    let root = self.inner_slow_build_root()$($await)*?;

                    let height = self.height()$($await)*;
                    Ok(CompressedCurveTreeRoot::from_root_node(height, root)?)
                }
            }

            pub $($async_fn)* fn root_node(
                &self,
            ) -> Result<Root<L, M, C::P0, C::P1>, Error> {
                self.inner_slow_build_root()$($await)*
            }

            $($async_fn)* fn inner_slow_build_root(
                &self,
            ) -> Result<Root<L, M, C::P0, C::P1>, Error> {
                let params = self.parameters();
                let root = NodeLocation::<L>::root(self.height()$($await)*);
                match self.backend.get_inner_node(root, None)$($await)*? {
                    Some(node) => match node.decompress()? {
                        Inner::Even(commitments) => Ok(Root::Even(RootNode {
                            commitments: commitments.clone(),
                            x_coord_children: self
                                ._get_odd_x_coord_children_batch(root, &params.odd_parameters.delta)
                                $($await)*?,
                        })),
                        Inner::Odd(commitments) => Ok(Root::Odd(RootNode {
                            commitments: commitments.clone(),
                            x_coord_children: self
                                ._get_even_x_coord_children_batch(root, &params.even_parameters.delta)
                                $($await)*?,
                        })),
                    }
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
                let root = self.get_or_init_root()$($await)*?;
                let block_number = self.backend.store_root(root)$($await)*?;
                Ok(block_number)
            }

            pub $($async_fn)* fn fetch_root(&self, block_number: Option<BlockNumber>) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
                self.backend.fetch_root(block_number)$($await)*.map_err(|_| crate::Error::CurveTreeRootNotFound.into())
            }

            pub $($async_fn)* fn get_path_to_leaf(
                &self,
                leaf_index: LeafIndex,
                tree_index: TreeIndex,
                block_number: Option<BlockNumber>,
            ) -> Result<CurveTreeWitnessPath<L, C::P0, C::P1>, Error> {
                let height = self.height()$($await)*;
                let mut even_internal_nodes = Vec::with_capacity(height as usize);
                let mut odd_internal_nodes = Vec::with_capacity(height as usize);

                let mut even_child = self
                    .backend
                    .get_leaf(leaf_index, block_number)
                    $($await)*?
                    .and_then(|leaf| leaf.decompress().ok())
                    .ok_or_else(|| crate::Error::CurveTreeLeafIndexOutOfBounds(leaf_index).into())?;
                let mut odd_child = Affine::<C::P1>::zero();

                // Start at the leaf's location.
                let mut location = NodeLocation::<L>::leaf(leaf_index);

                // Get the parameters for the tree.
                let params = self.parameters();

                while !location.is_root(height) {
                    let (parent_location, _) = location.parent();
                    let node = self
                        .backend
                        .get_inner_node(parent_location, block_number)
                        $($await)*?
                        .ok_or_else(|| crate::Error::CurveTreeNodeNotFound {
                            level: parent_location.level(),
                            index: parent_location.index(),
                        }.into())?;

                    match node.decompress()? {
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
                new_leaf_value: CompressedLeafValue<C>,
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
                let mut current_root = self.get_or_init_root()$($await)*?;

                while leaf_index < leaf_count {
                    let leaf_value = self
                        .backend
                        .get_leaf(leaf_index, None)
                        $($await)*?
                        .ok_or_else(|| crate::Error::CurveTreeLeafIndexOutOfBounds(leaf_index).into())?;

                    let mut even_old_child = None;
                    let mut even_new_child = CompressedChildCommitments::Leaf(leaf_value.into());
                    let mut odd_old_child = None;
                    let mut odd_new_child = CompressedChildCommitments::zero::<C::P1>();

                    // Start at the leaf's location.
                    let mut location = NodeLocation::<L>::leaf(leaf_index);
                    let mut is_root = location.is_root(height);
                    let mut child_is_leaf = true;

                    leaf_index += 1;
                    // Keep going until we reach the root of the tree.
                    while !is_root {
                        // Move to the parent location and get the child index of the current node.
                        let (parent_location, mut child_index) = location.parent();
                        location = parent_location;
                        is_root = location.is_root(height);

                        // Get or initialize the node at this location.
                        let mut node = match self.backend.get_inner_node(location, None)$($await)*? {
                            Some(node) => {
                                // Save the old commitments for the next level up.
                                if node.is_even {
                                    even_old_child = Some(CompressedChildCommitments::Inner(node.commitments));
                                } else {
                                    odd_old_child = Some(CompressedChildCommitments::Inner(node.commitments));
                                }
                                node
                            },
                            None => {
                                if location.is_even() {
                                    even_old_child = None;
                                    // Create a new even node with zero commitments.
                                    CompressedInner::default_even()
                                } else {
                                    odd_old_child = None;
                                    // Create a new odd node with zero commitments.
                                    CompressedInner::default_odd()
                                }
                            }
                        };

                        if node.is_even {
                            let new_x_coords = B::Updater::update_node(
                                &mut node,
                                child_index,
                                odd_old_child,
                                odd_new_child,
                            )?;

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
                            let new_x_coords = B::Updater::update_node(
                                &mut node,
                                child_index,
                                even_old_child,
                                even_new_child,
                            )?;

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
                                while child_index < L as ChildIndex - 1 && leaf_index < leaf_count {
                                    // Commit the next child leaf.
                                    child_index += 1;
                                    // Get the next uncommitted leaf.
                                    let leaf_value = self
                                        .backend
                                        .get_leaf(leaf_index, None)
                                        $($await)*?
                                        .ok_or_else(|| crate::Error::CurveTreeLeafIndexOutOfBounds(leaf_index).into())?;
                                    even_old_child = None;
                                    even_new_child = CompressedChildCommitments::Leaf(leaf_value.into());
                                    leaf_index += 1;

                                    let new_x_coords = B::Updater::update_node(
                                        &mut node,
                                        child_index,
                                        even_old_child,
                                        even_new_child,
                                    )?;

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

                // Store the updated root.
                self.backend.store_root(current_root)$($await)*?;

                Ok(true)
            }

            $($async_fn)* fn update_tree(
                &mut self,
                leaf_index: LeafIndex,
                old_leaf_value: Option<CompressedLeafValue<C>>,
                new_leaf_value: CompressedLeafValue<C>,
            ) -> Result<(), Error> {
                let height = self.height()$($await)*;
                let mut current_root = self.get_or_init_root()$($await)*?;

                let mut even_old_child = old_leaf_value.map(CompressedChildCommitments::leaf);
                let mut even_new_child = CompressedChildCommitments::leaf(new_leaf_value);
                let mut odd_old_child = None;
                let mut odd_new_child = CompressedChildCommitments::zero::<C::P1>();

                // Start at the leaf's location.
                let mut location = NodeLocation::<L>::leaf(leaf_index);
                let mut is_root = location.is_root(height);

                // Keep going until we reach the root of the tree.
                while !is_root {
                    // Move to the parent location and get the child index of the current node.
                    let (parent_location, child_index) = location.parent();
                    location = parent_location;
                    is_root = location.is_root(height);

                    let mut node = match self.backend.get_inner_node(location, None)$($await)*? {
                        Some(node) => {
                            // Save the old commitments for the next level up.
                            if node.is_even {
                                even_old_child = Some(CompressedChildCommitments::Inner(node.commitments));
                            } else {
                                odd_old_child = Some(CompressedChildCommitments::Inner(node.commitments));
                            }
                            node
                        },
                        None => {
                            if location.is_even() {
                                even_old_child = None;
                                // Create a new even node with zero commitments.
                                CompressedInner::default_even()
                            } else {
                                odd_old_child = None;
                                // Create a new odd node with zero commitments.
                                CompressedInner::default_odd()
                            }
                        }
                    };
                    let new_x_coords = if node.is_even {
                        let new_x_coords = B::Updater::update_node(
                            &mut node,
                            child_index,
                            odd_old_child,
                            odd_new_child,
                        )?;

                        // Save the new commitments for the next level up.
                        even_new_child = CompressedChildCommitments::Inner(node.commitments);

                        new_x_coords
                    } else {
                        let new_x_coords = B::Updater::update_node(
                            &mut node,
                            child_index,
                            even_old_child,
                            even_new_child,
                        )?;

                        // Save the new commitments for the next level up.
                        odd_new_child = CompressedChildCommitments::Inner(node.commitments);

                        new_x_coords
                    };

                    // Update the root
                    if is_root {
                        current_root.compressed_update(
                            node.commitments,
                            new_x_coords,
                            child_index,
                        )?;
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

                // Store the updated root.
                self.backend.store_root(current_root)$($await)*?;
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
                let block_number = self.get_block_number()$($await)*?;
                // Get the leaf and path for the given leaf index.
                let leaf = self
                    .get_leaf(leaf_index, Some(block_number))
                    $($await)*?
                    .ok_or_else(|| crate::Error::LeafIndexNotFound(leaf_index))?;
                let path = self.get_path_to_leaf(leaf_index, 0, Some(block_number))$($await)*?;
                let root = self.fetch_root(Some(block_number))$($await)*?;
                Ok(LeafPathAndRoot {
                    leaf,
                    leaf_index,
                    path: WrappedCanonical::wrap(&path)?,
                    block_number,
                    root: root.encode(),
                })
            }
        }
    };
}

#[derive(Clone, Copy, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct CompressedLeafValue<C: CurveTreeConfig> {
    point: CompressedAffine,
    #[codec(skip)]
    _marker: core::marker::PhantomData<C>,
}

impl<C: CurveTreeConfig> CompressedLeafValue<C> {
    pub fn new(point: CompressedAffine) -> Self {
        Self {
            point,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn zero() -> Self {
        let affine = Affine::<C::P0>::zero();
        Self::from_affine(affine).expect("Failed to convert zero Affine to CompressedAffine")
    }

    pub fn from_affine(point: Affine<C::P0>) -> Result<Self, Error> {
        let compressed: CompressedAffine = point.try_into()?;
        Ok(Self::new(compressed))
    }

    pub fn decompress(&self) -> Result<Affine<C::P0>, Error> {
        let point: Affine<C::P0> = (&self.point).try_into()?;
        Ok(point)
    }
}

impl<C: CurveTreeConfig> From<CompressedAffine> for CompressedLeafValue<C> {
    fn from(point: CompressedAffine) -> Self {
        Self::new(point)
    }
}

impl<C: CurveTreeConfig> From<CompressedLeafValue<C>> for CompressedAffine {
    fn from(value: CompressedLeafValue<C>) -> Self {
        value.point
    }
}
