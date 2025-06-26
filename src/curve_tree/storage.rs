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

struct TreeUpdaterState<
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
pub struct LeafValue<P0: SWCurveConfig>(Affine<P0>);

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

pub trait CurveTreeBackend<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig>:
    std::fmt::Debug
{
    fn height(&self) -> usize;

    fn set_height(&mut self, height: usize) -> Result<()>;

    fn allocate_leaf_index(&mut self) -> usize;

    fn get_leaf(&self, leaf_index: usize) -> Result<Option<LeafValue<P0>>>;

    fn set_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>>;

    fn leaf_count(&self) -> usize;

    fn get_inner_node(&self, location: NodeLocation<L>) -> Result<Option<Inner<M, P0, P1>>>;

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> Result<()>;
}

pub struct CurveTreeMemoryBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField>,
> {
    height: usize,
    leafs: Vec<LeafValue<P0>>,
    next_leaf_index: usize,
    nodes: HashMap<NodeLocation<L>, Inner<M, P0, P1>>,
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> std::fmt::Debug for CurveTreeMemoryBackend<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_struct("CurveTreeMemoryBackend")
            .field("height", &self.height())
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
> CurveTreeBackend<L, M, P0, P1> for CurveTreeMemoryBackend<L, M, P0, P1>
{
    fn height(&self) -> usize {
        self.height
    }

    fn set_height(&mut self, height: usize) -> Result<()> {
        self.height = height;
        Ok(())
    }

    fn allocate_leaf_index(&mut self) -> usize {
        let leaf_index = self.next_leaf_index;
        self.next_leaf_index += 1;
        leaf_index
    }

    fn get_leaf(&self, leaf_index: usize) -> Result<Option<LeafValue<P0>>> {
        Ok(self.leafs.get(leaf_index).copied())
    }

    fn set_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>> {
        let old_leaf_value = if let Some(leaf) = self.leafs.get_mut(leaf_index) {
            let old = *leaf;
            *leaf = new_leaf_value;
            Some(old)
        } else {
            self.leafs.push(new_leaf_value);
            None
        };
        Ok(old_leaf_value)
    }

    fn leaf_count(&self) -> usize {
        self.leafs.len()
    }

    fn get_inner_node(&self, location: NodeLocation<L>) -> Result<Option<Inner<M, P0, P1>>> {
        Ok(self.nodes.get(&location).copied())
    }

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> Result<()> {
        self.nodes.insert(location, new_node);
        Ok(())
    }
}

pub struct CurveTreeWithBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig,
> {
    backend: Box<dyn CurveTreeBackend<L, M, P0, P1> + Send>,
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> std::fmt::Debug for CurveTreeWithBackend<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt.debug_struct("CurveTreeStorage")
            .field("backend", &self.backend)
            .finish()
    }
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> CurveTreeWithBackend<L, M, P0, P1>
{
    pub fn new(height: usize, parameters: &SelRerandParameters<P0, P1>) -> Result<Self> {
        let mut tree = Self {
            backend: Box::new(CurveTreeMemoryBackend {
                height,
                leafs: vec![],
                next_leaf_index: 0,
                nodes: HashMap::new(),
            }),
        };
        tree.update_leaf(0, LeafValue::default(), parameters)?;
        Ok(tree)
    }

    pub fn new_with_backend(
        backend: Box<dyn CurveTreeBackend<L, M, P0, P1> + Send>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Self> {
        let mut tree = Self { backend };
        tree.update_leaf(0, LeafValue::default(), parameters)?;
        Ok(tree)
    }

    pub fn height(&self) -> usize {
        self.backend.height()
    }

    pub fn insert_leaf(
        &mut self,
        leaf_value: LeafValue<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<usize> {
        let leaf_index = self.backend.allocate_leaf_index();
        self.update_leaf(leaf_index, leaf_value, parameters)?;
        Ok(leaf_index)
    }

    pub fn get_leaf(&self, leaf_index: usize) -> Result<Option<LeafValue<P0>>> {
        self.backend.get_leaf(leaf_index)
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
            let x_coord = match self.backend.get_inner_node(child)? {
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
                self.backend.get_leaf(leaf_index)?.map(|leaf| leaf.0)
            } else {
                match self.backend.get_inner_node(child)? {
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
        let root = NodeLocation::<L>::root(self.height());
        match self.backend.get_inner_node(root)? {
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
        let mut even_internal_nodes = Vec::with_capacity(self.height());
        let mut odd_internal_nodes = Vec::with_capacity(self.height());

        let mut even_child = self
            .backend
            .get_leaf(leaf_index)?
            .map(|leaf| leaf.0)
            .ok_or_else(|| Error::CurveTreeLeafIndexOutOfBounds(leaf_index))?;
        let mut odd_child = Affine::<P1>::zero();

        // Start at the leaf's location.
        let mut location = NodeLocation::<L>::leaf(leaf_index);

        while !location.is_root(self.height()) {
            let (parent_location, _) = location.parent();
            let node = self
                .backend
                .get_inner_node(parent_location)?
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

    pub fn update_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: LeafValue<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<()> {
        let height = self.height();
        // Update the leaf to the new value and get the old value.
        let old_leaf_value = self.backend.set_leaf(leaf_index, new_leaf_value)?;

        let mut updater_state = TreeUpdaterState::<L, M, P0, P1>::new(
            leaf_index,
            old_leaf_value,
            new_leaf_value,
            height,
            parameters,
        )?;

        // Keep going until we reach the root of the tree.
        while !updater_state.is_root() {
            // Move to the parent location and get the child index of the current node.
            let location = updater_state.move_to_parent()?;

            let node = updater_state.update_node(self.backend.get_inner_node(location)?)?;
            // Save the updated node back to the backend.
            self.backend.set_inner_node(location, node)?;
        }

        // Check if the tree has grown to accommodate the new leaf.
        // if the root's level is higher than the current height, we need to update the height.
        let location = updater_state.location;
        if location.level() > height {
            log::warn!(
                "Tree height increased from {} to {}",
                height,
                location.level()
            );
            self.backend.set_height(location.level())?;
        }
        Ok(())
    }
}
