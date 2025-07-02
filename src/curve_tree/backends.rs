use std::collections::HashMap;

use ark_ec::models::short_weierstrass::SWCurveConfig;

use super::common::*;
use crate::{LeafIndex, NodeLevel, error::*};

pub trait CurveTreeBackend<const L: usize, const M: usize, P0: SWCurveConfig, P1: SWCurveConfig>:
    std::fmt::Debug
{
    type Error: From<crate::Error>;

    fn height(&self) -> NodeLevel;

    fn set_height(&mut self, height: NodeLevel) -> Result<(), Self::Error>;

    fn allocate_leaf_index(&mut self) -> LeafIndex;

    fn get_leaf(&self, leaf_index: LeafIndex) -> Result<Option<LeafValue<P0>>, Self::Error>;

    fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>, Self::Error>;

    fn leaf_count(&self) -> LeafIndex;

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> Result<Option<Inner<M, P0, P1>>, Self::Error>;

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> Result<(), Self::Error>;
}

#[cfg(feature = "async_tree")]
pub trait AsyncCurveTreeBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig,
>: std::fmt::Debug
{
    type Error: From<crate::Error>;

    fn height(&self) -> impl Future<Output = NodeLevel> + Send;

    fn set_height(
        &mut self,
        height: NodeLevel,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send;

    fn allocate_leaf_index(&mut self) -> impl Future<Output = LeafIndex> + Send;

    fn get_leaf(
        &self,
        leaf_index: LeafIndex,
    ) -> impl Future<Output = Result<Option<LeafValue<P0>>, Self::Error>> + Send;

    fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: LeafValue<P0>,
    ) -> impl Future<Output = Result<Option<LeafValue<P0>>, Self::Error>> + Send;

    fn leaf_count(&self) -> impl Future<Output = LeafIndex> + Send;

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> impl Future<Output = Result<Option<Inner<M, P0, P1>>, Self::Error>> + Send;

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send;
}

pub struct CurveTreeMemoryBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField>,
> {
    height: NodeLevel,
    leafs: Vec<LeafValue<P0>>,
    next_leaf_index: LeafIndex,
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
    pub fn new(height: NodeLevel) -> Self {
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
    type Error = Error;

    fn height(&self) -> NodeLevel {
        self.height
    }

    fn set_height(&mut self, height: NodeLevel) -> Result<(), Error> {
        self.height = height;
        Ok(())
    }

    fn allocate_leaf_index(&mut self) -> LeafIndex {
        let leaf_index = self.next_leaf_index;
        self.next_leaf_index += 1;
        leaf_index
    }

    fn get_leaf(&self, leaf_index: LeafIndex) -> Result<Option<LeafValue<P0>>, Error> {
        Ok(self.leafs.get(leaf_index as usize).copied())
    }

    fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>, Error> {
        let old_leaf_value = if let Some(leaf) = self.leafs.get_mut(leaf_index as usize) {
            let old = *leaf;
            *leaf = new_leaf_value;
            Some(old)
        } else {
            self.leafs.push(new_leaf_value);
            None
        };
        Ok(old_leaf_value)
    }

    fn leaf_count(&self) -> LeafIndex {
        self.leafs.len() as LeafIndex
    }

    fn get_inner_node(&self, location: NodeLocation<L>) -> Result<Option<Inner<M, P0, P1>>, Error> {
        Ok(self.nodes.get(&location).copied())
    }

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> Result<(), Error> {
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
    type Error = Error;

    async fn height(&self) -> NodeLevel {
        (self as &dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>).height()
    }

    async fn set_height(&mut self, height: NodeLevel) -> Result<(), Error> {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>).set_height(height)
    }

    async fn allocate_leaf_index(&mut self) -> LeafIndex {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>).allocate_leaf_index()
    }

    async fn get_leaf(&self, leaf_index: LeafIndex) -> Result<Option<LeafValue<P0>>, Error> {
        (self as &dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>).get_leaf(leaf_index)
    }

    async fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>, Error> {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>)
            .set_leaf(leaf_index, new_leaf_value)
    }

    async fn leaf_count(&self) -> LeafIndex {
        (self as &dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>).leaf_count()
    }

    async fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> Result<Option<Inner<M, P0, P1>>, Error> {
        (self as &dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>).get_inner_node(location)
    }

    async fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> Result<(), Error> {
        (self as &mut dyn CurveTreeBackend<L, M, P0, P1, Error = Self::Error>)
            .set_inner_node(location, new_node)
    }
}
