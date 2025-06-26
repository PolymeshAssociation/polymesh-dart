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

pub trait AsyncCurveTreeBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig,
>: std::fmt::Debug
{
    fn height(&self) -> impl Future<Output = usize> + Send;

    fn set_height(&mut self, height: usize) -> impl Future<Output = Result<(), Error>> + Send;

    fn allocate_leaf_index(&mut self) -> impl Future<Output = usize> + Send;

    fn get_leaf(
        &self,
        leaf_index: usize,
    ) -> impl Future<Output = Result<Option<LeafValue<P0>>, Error>> + Send;

    fn set_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: LeafValue<P0>,
    ) -> impl Future<Output = Result<Option<LeafValue<P0>>, Error>> + Send;

    fn leaf_count(&self) -> impl Future<Output = usize> + Send;

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> impl Future<Output = Result<Option<Inner<M, P0, P1>>, Error>> + Send;

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> impl Future<Output = Result<(), Error>> + Send;
}

pub struct AsyncCurveTreeWithBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig,
    B: AsyncCurveTreeBackend<L, M, P0, P1>,
> {
    backend: B,
    _phantom: std::marker::PhantomData<(P0, P1)>,
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
    B: AsyncCurveTreeBackend<L, M, P0, P1> + Send,
> std::fmt::Debug for AsyncCurveTreeWithBackend<L, M, P0, P1, B>
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
> AsyncCurveTreeWithBackend<L, M, P0, P1, CurveTreeMemoryBackend<L, M, P0, P1>>
{
    pub async fn new(
        height: usize,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Self, Error> {
        Self::new_with_backend(CurveTreeMemoryBackend::new(height), parameters).await
    }
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
    B: AsyncCurveTreeBackend<L, M, P0, P1> + Send,
> AsyncCurveTreeWithBackend<L, M, P0, P1, B>
{
    pub async fn new_with_backend(
        backend: B,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Self, Error> {
        let mut tree = Self {
            backend,
            _phantom: std::marker::PhantomData,
        };
        tree.update_leaf(0, LeafValue::default(), parameters)
            .await?;
        Ok(tree)
    }

    pub async fn height(&self) -> usize {
        self.backend.height().await
    }

    pub async fn insert_leaf(
        &mut self,
        leaf_value: LeafValue<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<usize, Error> {
        let leaf_index = self.backend.allocate_leaf_index().await;
        self.update_leaf(leaf_index, leaf_value, parameters).await?;
        Ok(leaf_index)
    }

    pub async fn get_leaf(&self, leaf_index: usize) -> Result<Option<LeafValue<P0>>, Error> {
        self.backend.get_leaf(leaf_index).await
    }

    async fn _get_odd_x_coord_children_batch(
        &self,
        parent: NodeLocation<L>,
        delta: &Affine<P1>,
    ) -> Result<Vec<[P1::BaseField; L]>, Error> {
        let mut batch_x_coord_children = Vec::with_capacity(M);
        for tree_index in 0..M {
            let x_coord_children = self
                ._get_odd_x_coord_children(tree_index, parent, delta)
                .await?;
            batch_x_coord_children.push(x_coord_children);
        }
        Ok(batch_x_coord_children)
    }

    async fn _get_odd_x_coord_children(
        &self,
        tree_index: usize,
        parent: NodeLocation<L>,
        delta: &Affine<P1>,
    ) -> Result<[P1::BaseField; L], Error> {
        let mut x_coord_children = [P1::BaseField::zero(); L];
        for idx in 0..L {
            let child = parent.child(idx)?;
            let x_coord = match self.backend.get_inner_node(child).await? {
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

    async fn _get_even_x_coord_children_batch(
        &self,
        parent: NodeLocation<L>,
        delta: &Affine<P0>,
    ) -> Result<Vec<[P0::BaseField; L]>, Error> {
        let mut batch_x_coord_children = Vec::with_capacity(M);
        for tree_index in 0..M {
            let x_coord_children = self
                ._get_even_x_coord_children(tree_index, parent, delta)
                .await?;
            batch_x_coord_children.push(x_coord_children);
        }
        Ok(batch_x_coord_children)
    }

    async fn _get_even_x_coord_children(
        &self,
        tree_index: usize,
        parent: NodeLocation<L>,
        delta: &Affine<P0>,
    ) -> Result<[P0::BaseField; L], Error> {
        let mut x_coord_children = [P0::BaseField::zero(); L];
        for idx in 0..L {
            let child = parent.child(idx)?;
            let commitment = if let NodeLocation::Leaf(leaf_index) = child {
                self.backend.get_leaf(leaf_index).await?.map(|leaf| leaf.0)
            } else {
                match self.backend.get_inner_node(child).await? {
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

    pub async fn root_node(
        &self,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<Root<L, M, P0, P1>, Error> {
        let root = NodeLocation::<L>::root(self.height().await);
        match self.backend.get_inner_node(root).await? {
            Some(Inner::Even(commitments)) => Ok(Root::Even(RootNode {
                commitments: commitments.clone(),
                x_coord_children: self
                    ._get_odd_x_coord_children_batch(root, &parameters.odd_parameters.delta)
                    .await?,
            })),
            Some(Inner::Odd(commitments)) => Ok(Root::Odd(RootNode {
                commitments: commitments.clone(),
                x_coord_children: self
                    ._get_even_x_coord_children_batch(root, &parameters.even_parameters.delta)
                    .await?,
            })),
            None => Err(Error::CurveTreeRootNotFound),
        }
    }

    pub async fn get_path_to_leaf(
        &self,
        leaf_index: usize,
        tree_index: usize,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<CurveTreeWitnessPath<L, P0, P1>, Error> {
        let height = self.height().await;
        let mut even_internal_nodes = Vec::with_capacity(height);
        let mut odd_internal_nodes = Vec::with_capacity(height);

        let mut even_child = self
            .backend
            .get_leaf(leaf_index)
            .await?
            .map(|leaf| leaf.0)
            .ok_or_else(|| Error::CurveTreeLeafIndexOutOfBounds(leaf_index))?;
        let mut odd_child = Affine::<P1>::zero();

        // Start at the leaf's location.
        let mut location = NodeLocation::<L>::leaf(leaf_index);

        while !location.is_root(height) {
            let (parent_location, _) = location.parent();
            let node = self
                .backend
                .get_inner_node(parent_location)
                .await?
                .ok_or_else(|| Error::CurveTreeNodeNotFound {
                    level: parent_location.level(),
                    index: parent_location.index(),
                })?;

            match node {
                Inner::Even(commitments) => {
                    even_child = commitments[tree_index];
                    even_internal_nodes.push(WitnessNode {
                        x_coord_children: self
                            ._get_odd_x_coord_children(
                                tree_index,
                                parent_location,
                                &parameters.odd_parameters.delta,
                            )
                            .await?,
                        child_node_to_randomize: odd_child,
                    });
                }
                Inner::Odd(commitments) => {
                    odd_child = commitments[tree_index];
                    odd_internal_nodes.push(WitnessNode {
                        x_coord_children: self
                            ._get_even_x_coord_children(
                                tree_index,
                                parent_location,
                                &parameters.even_parameters.delta,
                            )
                            .await?,
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

    pub async fn update_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: LeafValue<P0>,
        parameters: &SelRerandParameters<P0, P1>,
    ) -> Result<(), Error> {
        let height = self.height().await;
        // Update the leaf to the new value and get the old value.
        let old_leaf_value = self.backend.set_leaf(leaf_index, new_leaf_value).await?;

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

            let node = updater_state.update_node(self.backend.get_inner_node(location).await?)?;
            // Save the updated node back to the backend.
            self.backend.set_inner_node(location, node).await?;
        }

        // Check if the tree has grown to accommodate the new leaf.
        // if the root's level is higher than the current height, we need to update the height.
        if let Some(new_height) = updater_state.is_new_height() {
            self.backend.set_height(new_height).await?;
        }
        Ok(())
    }
}
