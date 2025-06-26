use ark_ec::AffineRepr;
use ark_ec::{CurveGroup, models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_std::Zero;
use curve_tree_relations::{
    curve_tree::{Root, RootNode, SelRerandParameters},
    curve_tree_prover::{CurveTreeWitnessPath, WitnessNode},
};

use super::backends::CurveTreeMemoryBackend;
use super::common::*;
use crate::error::*;

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
            backend: Box::new(CurveTreeMemoryBackend::new(height)),
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
        if let Some(new_height) = updater_state.is_new_height() {
            self.backend.set_height(new_height)?;
        }
        Ok(())
    }
}
