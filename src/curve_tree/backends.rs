use std::collections::HashMap;

use ark_ec::models::short_weierstrass::SWCurveConfig;

use super::common::*;
use super::sync_tree::CurveTreeBackend;
#[cfg(feature = "async_tree")]
use crate::curve_tree::async_tree::AsyncCurveTreeBackend;
use crate::error::*;

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
> CurveTreeMemoryBackend<L, M, P0, P1>
{
    pub fn new(height: usize) -> Self {
        Self {
            height,
            leafs: Vec::new(),
            next_leaf_index: 0,
            nodes: HashMap::new(),
        }
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

#[cfg(feature = "async_tree")]
impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> AsyncCurveTreeBackend<L, M, P0, P1> for CurveTreeMemoryBackend<L, M, P0, P1>
{
    async fn height(&self) -> usize {
        (self as &dyn CurveTreeBackend<L, M, P0, P1>).height()
    }

    async fn set_height(&mut self, height: usize) -> Result<()> {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1>).set_height(height)
    }

    async fn allocate_leaf_index(&mut self) -> usize {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1>).allocate_leaf_index()
    }

    async fn get_leaf(&self, leaf_index: usize) -> Result<Option<LeafValue<P0>>> {
        (self as &dyn CurveTreeBackend<L, M, P0, P1>).get_leaf(leaf_index)
    }

    async fn set_leaf(
        &mut self,
        leaf_index: usize,
        new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>> {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1>).set_leaf(leaf_index, new_leaf_value)
    }

    async fn leaf_count(&self) -> usize {
        (self as &dyn CurveTreeBackend<L, M, P0, P1>).leaf_count()
    }

    async fn get_inner_node(&self, location: NodeLocation<L>) -> Result<Option<Inner<M, P0, P1>>> {
        (self as &dyn CurveTreeBackend<L, M, P0, P1>).get_inner_node(location)
    }

    async fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> Result<()> {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1>).set_inner_node(location, new_node)
    }
}
