use ark_ec::models::short_weierstrass::SWCurveConfig;
use ark_std::{collections::BTreeMap, vec::Vec};
use curve_tree_relations::curve_tree::{
    Root,
    SelRerandParameters
};

use super::common::*;
use crate::{
    BlockNumber, LeafIndex, NodeLevel, PallasParameters,
    curve_tree::{CurveTreeLookup, CurveTreeParameters, CurveTreePath, CurveTreeRoot},
    error::*,
};

pub struct LeafPathAndRoot<'p, const L: usize, Block> {
    pub leaf: LeafValue<PallasParameters>,
    pub leaf_index: LeafIndex,
    pub path: CurveTreePath<L>,
    pub block_number: Block,
    pub root: CurveTreeRoot<L>,
    pub params: &'p CurveTreeParameters,
}

impl<'p, const L: usize, Block: From<BlockNumber> + TryInto<BlockNumber> + Copy> CurveTreeLookup<L> for LeafPathAndRoot<'p, L, Block> {
    type BlockNumber = Block;

    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L>, Error> {
        if self.leaf_index == leaf_index {
            Ok(self.path.clone())
        } else {
            Err(Error::LeafIndexNotFound(leaf_index))
        }
    }

    fn get_path_to_leaf(
        &self,
        leaf: LeafValue<PallasParameters>,
    ) -> Result<CurveTreePath<L>, Error> {
        if self.leaf == leaf {
            Ok(self.path.clone())
        } else {
            Err(Error::LeafNotFound(leaf))
        }
    }

    fn params(&self) -> &CurveTreeParameters {
        self.params
    }

    fn root_node(&self) -> Result<CurveTreeRoot<L>, Error> {
        Ok(self.root.clone())
    }

    fn get_block_number(&self) -> Result<Block, Error> {
        Ok(self.block_number)
    }
}

pub trait CurveTreeBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
>: Sized
{
    type Error: From<crate::Error>;
    type BlockNumber: From<BlockNumber> + TryInto<BlockNumber> + Copy;

    fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Self::Error>;

    fn parameters(&self) -> &SelRerandParameters<P0, P1>;

    fn get_block_number(&self) -> Result<Self::BlockNumber, Self::Error>;

    fn set_block_number(&mut self, _block_number: Self::BlockNumber) -> Result<(), Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn store_root(&mut self, _root: Root<L, M, P0, P1>) -> Result<Self::BlockNumber, Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn fetch_root(
        &self,
        block_number: Self::BlockNumber,
    ) -> Result<Root<L, M, P0, P1>, Self::Error>;

    fn height(&self) -> NodeLevel;

    fn set_height(&mut self, _height: NodeLevel) -> Result<(), Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn allocate_leaf_index(&mut self) -> LeafIndex;

    fn get_leaf(&self, leaf_index: LeafIndex) -> Result<Option<LeafValue<P0>>, Self::Error>;

    fn set_leaf(
        &mut self,
        _leaf_index: LeafIndex,
        _new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>, Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn leaf_count(&self) -> LeafIndex;

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> Result<Option<Inner<M, P0, P1>>, Self::Error>;

    fn set_inner_node(
        &mut self,
        _location: NodeLocation<L>,
        _new_node: Inner<M, P0, P1>,
    ) -> Result<(), Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }
}

#[cfg(feature = "async_tree")]
pub trait AsyncCurveTreeBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig + Copy,
>: Sized
{
    type Error: From<crate::Error>;
    type BlockNumber: From<BlockNumber> + TryInto<BlockNumber> + Copy;

    fn new(
        height: NodeLevel,
        gens_length: usize,
    ) -> impl Future<Output = Result<Self, Self::Error>> + Send;

    fn parameters(&self) -> impl Future<Output = &SelRerandParameters<P0, P1>> + Send;

    fn get_block_number(
        &self,
    ) -> impl Future<Output = Result<Self::BlockNumber, Self::Error>> + Send;

    fn set_block_number(&mut self, _block_number: Self::BlockNumber) -> impl Future<Output = Result<(), Self::Error>> + Send {
        async move {
            Err(Error::CurveTreeBackendReadOnly.into())
        }
    }

    fn store_root(
        &mut self,
        _root: Root<L, M, P0, P1>,
    ) -> impl Future<Output = Result<Self::BlockNumber, Self::Error>> + Send {
        async move {
            Err(Error::CurveTreeBackendReadOnly.into())
        }
    }

    fn fetch_root(
        &self,
        block_number: Self::BlockNumber,
    ) -> impl Future<Output = Result<Root<L, M, P0, P1>, Self::Error>> + Send;

    fn height(&self) -> impl Future<Output = NodeLevel> + Send;

    fn set_height(
        &mut self,
        _height: NodeLevel,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send {
        async move {
            Err(Error::CurveTreeBackendReadOnly.into())
        }
    }

    fn allocate_leaf_index(&mut self) -> impl Future<Output = LeafIndex> + Send;

    fn get_leaf(
        &self,
        leaf_index: LeafIndex,
    ) -> impl Future<Output = Result<Option<LeafValue<P0>>, Self::Error>> + Send;

    fn set_leaf(
        &mut self,
        _leaf_index: LeafIndex,
        _new_leaf_value: LeafValue<P0>,
    ) -> impl Future<Output = Result<Option<LeafValue<P0>>, Self::Error>> + Send {
        async move {
            Err(Error::CurveTreeBackendReadOnly.into())
        }
    }

    fn leaf_count(&self) -> impl Future<Output = LeafIndex> + Send;

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> impl Future<Output = Result<Option<Inner<M, P0, P1>>, Self::Error>> + Send;

    fn set_inner_node(
        &mut self,
        _location: NodeLocation<L>,
        _new_node: Inner<M, P0, P1>,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send {
        async move {
            Err(Error::CurveTreeBackendReadOnly.into())
        }
    }
}

pub struct CurveTreeMemoryBackend<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy,
> {
    height: NodeLevel,
    leafs: Vec<LeafValue<P0>>,
    next_leaf_index: LeafIndex,
    nodes: BTreeMap<NodeLocation<L>, Inner<M, P0, P1>>,
    block_number: BlockNumber,
    roots: BTreeMap<BlockNumber, Root<L, M, P0, P1>>,
    parameters: SelRerandParameters<P0, P1>,
}

impl<
    const L: usize,
    const M: usize,
    P0: SWCurveConfig + Copy + Send,
    P1: SWCurveConfig<BaseField = P0::ScalarField, ScalarField = P0::BaseField> + Copy + Send,
> core::fmt::Debug for CurveTreeMemoryBackend<L, M, P0, P1>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("CurveTreeMemoryBackend")
            .field("height", &self.height)
            .field("leafs", &self.leafs)
            .field("next_leaf_index", &self.next_leaf_index)
            .field("nodes", &self.nodes)
            .field("block_number", &self.block_number)
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
    pub fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Error> {
        Ok(Self {
            height,
            leafs: Vec::new(),
            next_leaf_index: 0,
            nodes: BTreeMap::new(),
            block_number: 0,
            roots: BTreeMap::new(),
            parameters: SelRerandParameters::new(gens_length, gens_length)?,
        })
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
    type BlockNumber = BlockNumber;

    fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Self::Error> {
        Ok(CurveTreeMemoryBackend::new(height, gens_length)?)
    }

    fn parameters(&self) -> &SelRerandParameters<P0, P1> {
        &self.parameters
    }

    fn get_block_number(&self) -> Result<Self::BlockNumber, Self::Error> {
        Ok(self.block_number)
    }

    fn set_block_number(&mut self, block_number: Self::BlockNumber) -> Result<(), Self::Error> {
        self.block_number = block_number;
        Ok(())
    }

    fn store_root(&mut self, root: Root<L, M, P0, P1>) -> Result<Self::BlockNumber, Self::Error> {
        let block_number = self.block_number + 1;
        self.block_number = block_number;
        self.roots.insert(block_number, root);
        Ok(block_number)
    }

    fn fetch_root(
        &self,
        block_number: Self::BlockNumber,
    ) -> Result<Root<L, M, P0, P1>, Self::Error> {
        self.roots.get(&block_number).cloned()
            .ok_or(Error::CurveTreeRootNotFound)
    }

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
where
    Self: CurveTreeBackend<L, M, P0, P1, Error = Error>,
{
    type Error = Error;
    type BlockNumber = BlockNumber;

    async fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Self::Error> {
        Ok(CurveTreeMemoryBackend::new(height, gens_length)?)
    }

    async fn parameters(&self) -> &SelRerandParameters<P0, P1> {
        &self.parameters
    }

    async fn get_block_number(&self) -> Result<Self::BlockNumber, Self::Error> {
        Ok(self.block_number)
    }

    async fn set_block_number(&mut self, block_number: Self::BlockNumber) -> Result<(), Self::Error> {
        self.block_number = block_number;
        Ok(())
    }

    async fn store_root(
        &mut self,
        root: Root<L, M, P0, P1>,
    ) -> Result<Self::BlockNumber, Self::Error> {
        let block_number = self.block_number + 1;
        self.block_number = block_number;
        self.roots.insert(block_number, root);
        Ok(block_number)
    }

    async fn fetch_root(
        &self,
        block_number: Self::BlockNumber,
    ) -> Result<Root<L, M, P0, P1>, Self::Error> {
        self.roots.get(&block_number).cloned().ok_or(Error::CurveTreeRootNotFound)
    }

    async fn height(&self) -> NodeLevel {
        CurveTreeBackend::height(self)
    }

    async fn set_height(&mut self, height: NodeLevel) -> Result<(), Error> {
        CurveTreeBackend::set_height(self, height)
    }

    async fn allocate_leaf_index(&mut self) -> LeafIndex {
        CurveTreeBackend::allocate_leaf_index(self)
    }

    async fn get_leaf(&self, leaf_index: LeafIndex) -> Result<Option<LeafValue<P0>>, Error> {
        CurveTreeBackend::get_leaf(self, leaf_index)
    }

    async fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: LeafValue<P0>,
    ) -> Result<Option<LeafValue<P0>>, Error> {
        CurveTreeBackend::set_leaf(self, leaf_index, new_leaf_value)
    }

    async fn leaf_count(&self) -> LeafIndex {
        CurveTreeBackend::leaf_count(self)
    }

    async fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> Result<Option<Inner<M, P0, P1>>, Error> {
        CurveTreeBackend::get_inner_node(self, location)
    }

    async fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: Inner<M, P0, P1>,
    ) -> Result<(), Error> {
        CurveTreeBackend::set_inner_node(self, location, new_node)
    }
}
