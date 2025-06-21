use std::collections::HashMap;

use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use curve_tree_relations::{
    curve_tree::{Root, RootNode, SelRerandParameters},
    curve_tree_prover::{CurveTreeWitnessPath, WitnessNode},
    single_level_select_and_rerandomize::*,
};

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
                level == height && index == 0
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
    pub fn child(self, child_index: usize) -> Option<Self> {
        if child_index >= L {
            return None; // Invalid child index
        }
        match self {
            Self::Leaf(_) => None, // Leaf nodes do not have children
            Self::Odd { level: 1, index } => Some(Self::Leaf(index * L + child_index)),
            Self::Odd { level, index } => Some(Self::Even {
                level: level.saturating_add(1),
                index: index * L + child_index,
            }),
            Self::Even { level, index } => Some(Self::Odd {
                level: level.saturating_add(1),
                index: index * L + child_index,
            }),
        }
    }
}

fn default_inner_node<
    const L: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
>(
    old_child: Affine<P0>,
    delta: &Affine<P0>,
    parameters: &SingleLayerParameters<P1>,
) -> Affine<P1> {
    let x_coord = (old_child + delta).into_affine().x;
    parameters.commit_for_default_node(x_coord, L, 0)
}

fn update_inner_node<
    const L: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
>(
    commitment: &mut Affine<P1>,
    local_index: usize,
    old_child: Affine<P0>,
    new_child: Affine<P0>,
    delta: &Affine<P0>,
    parameters: &SingleLayerParameters<P1>,
) {
    let old_x_coord = (old_child + delta).into_affine().x;
    let new_x_coord = (new_child + delta).into_affine().x;
    let gen_iter = parameters.bp_gens.share(0).G(L).skip(local_index);
    let g = gen_iter.copied().next().unwrap();
    *commitment = (commitment.into_group() + g * (new_x_coord - old_x_coord)).into_affine();
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Inner<P0: SWCurveConfig, P1: SWCurveConfig> {
    Even(Affine<P0>),
    Odd(Affine<P1>),
}

impl<
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> Inner<P0, P1>
{
    pub fn zero_even() -> Self {
        Self::Even(Affine::<P0>::zero())
    }

    pub fn zero_odd() -> Self {
        Self::Odd(Affine::<P1>::zero())
    }

    pub fn default_even<const L: usize>(
        old_child: Affine<P1>,
        delta: &Affine<P1>,
        parameters: &SingleLayerParameters<P0>,
    ) -> Self {
        Self::Even(default_inner_node::<L, P1, P0>(
            old_child, delta, parameters,
        ))
    }

    pub fn default_odd<const L: usize>(
        old_child: Affine<P0>,
        delta: &Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) -> Self {
        Self::Odd(default_inner_node::<L, P0, P1>(
            old_child, delta, parameters,
        ))
    }

    pub fn update_even_node<const L: usize>(
        commitment: &mut Affine<P0>,
        local_index: usize,
        old_child: Affine<P1>,
        new_child: Affine<P1>,
        delta: &Affine<P1>,
        parameters: &SingleLayerParameters<P0>,
    ) {
        update_inner_node::<L, P1, P0>(
            commitment,
            local_index,
            old_child,
            new_child,
            delta,
            parameters,
        );
    }

    pub fn update_odd_node<const L: usize>(
        commitment: &mut Affine<P1>,
        local_index: usize,
        old_child: Affine<P0>,
        new_child: Affine<P0>,
        delta: &Affine<P0>,
        parameters: &SingleLayerParameters<P1>,
    ) {
        update_inner_node::<L, P0, P1>(
            commitment,
            local_index,
            old_child,
            new_child,
            delta,
            parameters,
        );
    }
}

pub struct CurveTreeNodeStorages<const L: usize, P0: SWCurveConfig, P1: SWCurveConfig> {
    pub height: usize,
    pub leafs: Vec<Affine<P0>>,
    pub nodes: HashMap<NodeLocation<L>, Inner<P0, P1>>,
}

impl<
    const L: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> CurveTreeNodeStorages<L, P0, P1>
{
    pub fn new(height: usize, parameters: &SelRerandParameters<P0, P1>) -> Self {
        let mut tree = Self {
            height,
            leafs: vec![Self::default_leaf_value()],
            nodes: HashMap::new(),
        };
        tree.update_leaf(0, Self::default_leaf_value(), parameters);
        tree
    }

    fn default_leaf_value() -> Affine<P0> {
        Affine::<P0>::zero()
    }

    pub fn insert_leaf(
        &mut self,
        leaf_value: Affine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) {
        let leaf_index = self.leafs.len();
        self.update_leaf(leaf_index, leaf_value, parameters);
    }

    pub fn get_leaf(&self, leaf_index: usize) -> Option<Affine<P0>> {
        self.leafs.get(leaf_index).copied()
    }

    fn _get_odd_x_coord_children(
        &self,
        parent: NodeLocation<L>,
        delta: &Affine<P1>,
    ) -> Option<[P1::BaseField; L]> {
        let mut x_coord_children = Vec::with_capacity(L);
        for idx in 0..L {
            let child = parent.child(idx)?;
            let x_coord = match self
                .nodes
                .get(&child)
                .copied()
                .unwrap_or_else(Inner::zero_even)
            {
                Inner::Odd(commitment) => (commitment + delta).into_affine().x,
                Inner::Even(_) => {
                    log::error!("An Even node cannot have an even child");
                    return None;
                }
            };
            x_coord_children.push(x_coord);
        }
        x_coord_children.try_into().ok()
    }

    fn _get_even_x_coord_children(
        &self,
        parent: NodeLocation<L>,
        delta: &Affine<P0>,
    ) -> Option<[P0::BaseField; L]> {
        let mut x_coord_children = Vec::with_capacity(L);
        for idx in 0..L {
            let child = parent.child(idx)?;
            let x_coord = match self
                .nodes
                .get(&child)
                .copied()
                .unwrap_or_else(Inner::zero_even)
            {
                Inner::Even(commitment) => (commitment + delta).into_affine().x,
                Inner::Odd(_) => {
                    log::error!("An Odd node cannot have an odd child");
                    return None;
                }
            };
            x_coord_children.push(x_coord);
        }
        x_coord_children.try_into().ok()
    }

    pub fn root_node(
        &self,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Option<Root<L, 1, P0, P1>> {
        let root = NodeLocation::<L>::root(self.height);
        match self.nodes.get(&root) {
            Some(Inner::Even(commitment)) => Some(Root::Even(RootNode {
                commitments: [commitment.clone()],
                x_coord_children: vec![
                    self._get_odd_x_coord_children(root, &parameters.odd_parameters.delta)?,
                ],
            })),
            Some(Inner::Odd(commitment)) => Some(Root::Odd(RootNode {
                commitments: [commitment.clone()],
                x_coord_children: vec![
                    self._get_even_x_coord_children(root, &parameters.even_parameters.delta)?,
                ],
            })),
            None => None,
        }
    }

    pub fn get_path_to_leaf(
        &self,
        leaf_index: usize,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Option<CurveTreeWitnessPath<L, P0, P1>> {
        let mut even_internal_nodes = Vec::with_capacity(self.height);
        let mut odd_internal_nodes = Vec::with_capacity(self.height);

        let mut even_child = *self.leafs.get(leaf_index)?;
        let mut odd_child = Affine::<P1>::zero();

        // Start at the leaf's location.
        let mut location = NodeLocation::<L>::leaf(leaf_index);

        while !location.is_root(self.height) {
            let (parent_location, _) = location.parent();
            let node = self.nodes.get(&parent_location)?;

            match node {
                Inner::Even(commitment) => {
                    even_child = *commitment;
                    even_internal_nodes.push(WitnessNode {
                        x_coord_children: self._get_odd_x_coord_children(
                            parent_location,
                            &parameters.odd_parameters.delta,
                        )?,
                        child_node_to_randomize: odd_child,
                    });
                }
                Inner::Odd(commitment) => {
                    odd_child = *commitment;
                    odd_internal_nodes.push(WitnessNode {
                        x_coord_children: self._get_even_x_coord_children(
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
        Some(CurveTreeWitnessPath {
            even_internal_nodes,
            odd_internal_nodes,
        })
    }

    fn get_node_mut(
        &mut self,
        parent_location: NodeLocation<L>,
        even_child: Affine<P0>,
        odd_child: Affine<P1>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> &mut Inner<P0, P1> {
        self.nodes.entry(parent_location).or_insert_with(|| {
            if parent_location.is_even() {
                Inner::default_even::<L>(
                    odd_child,
                    &parameters.odd_parameters.delta,
                    &parameters.even_parameters,
                )
            } else {
                Inner::default_odd::<L>(
                    even_child,
                    &parameters.even_parameters.delta,
                    &parameters.odd_parameters,
                )
            }
        })
    }

    pub fn update_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: Affine<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) {
        let old_leaf_value = if let Some(leaf) = self.leafs.get_mut(leaf_index) {
            let old = *leaf;
            *leaf = new_leaf_value;
            old
        } else if leaf_index == self.leafs.len() {
            // If the leaf index is equal to the current length, we are adding a new leaf.
            self.leafs.push(new_leaf_value);
            Self::default_leaf_value()
        } else {
            // TODO: return an error if the leaf index is out of bounds.
            return;
        };
        // Store the leaf as the even x-coordinate.
        let mut even_old_child = old_leaf_value;
        let mut even_new_child = new_leaf_value;
        // Use zeroes to initialize the odd commitments.
        let mut odd_old_child = Affine::<P1>::zero();
        let mut odd_new_child = Affine::<P1>::zero();

        // Start at the leaf's location.
        let mut location = NodeLocation::<L>::leaf(leaf_index);

        while !location.is_root(self.height) {
            let (parent_location, local_index) = location.parent();
            let node =
                self.get_node_mut(parent_location, even_old_child, odd_old_child, parameters);

            match node {
                Inner::Even(commitment) => {
                    even_old_child = *commitment;
                    Inner::update_even_node::<L>(
                        commitment,
                        local_index,
                        odd_old_child,
                        odd_new_child,
                        &parameters.odd_parameters.delta,
                        &parameters.even_parameters,
                    );
                    even_new_child = *commitment;
                }
                Inner::Odd(commitment) => {
                    odd_old_child = *commitment;
                    Inner::update_odd_node::<L>(
                        commitment,
                        local_index,
                        even_old_child,
                        even_new_child,
                        &parameters.even_parameters.delta,
                        &parameters.odd_parameters,
                    );
                    odd_new_child = *commitment;
                }
            }

            location = parent_location;
        }
    }
}
