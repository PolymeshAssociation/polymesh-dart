#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use ark_std::{collections::BTreeMap, vec::Vec};
use curve_tree_relations::curve_tree::SelRerandParameters;

use codec::{Decode, Encode};

use super::common::*;
use crate::{
    BlockNumber, LeafIndex, NodeLevel, WrappedCanonical,
    curve_tree::{
        CompressedCurveTreeRoot, CurveTreeConfig, CurveTreeLookup, CurveTreeParameters,
        CurveTreePath, CurveTreeUpdater, DefaultCurveTreeUpdater,
    },
    error::*,
};

#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MultiLeafPathAndRoot<const L: usize, const M: usize, C: CurveTreeConfig> {
    pub paths: Vec<LeafPathAndRoot<L, M, C>>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> MultiLeafPathAndRoot<L, M, C> {
    pub fn new() -> Self {
        Self { paths: Vec::new() }
    }

    pub fn first(&self) -> Option<&LeafPathAndRoot<L, M, C>> {
        self.paths.first()
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeLookup<L, M, C>
    for MultiLeafPathAndRoot<L, M, C>
{
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error> {
        for leaf_path in &self.paths {
            if leaf_path.leaf_index == leaf_index {
                return leaf_path.get_path();
            }
        }
        Err(Error::LeafIndexNotFound(leaf_index))
    }

    fn get_path_to_leaf(&self, leaf: CompressedLeafValue<C>) -> Result<CurveTreePath<L, C>, Error> {
        for leaf_path in &self.paths {
            if leaf_path.leaf == leaf {
                return leaf_path.get_path();
            }
        }
        Err(Error::LeafNotFound)
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        C::parameters()
    }

    fn root_node(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
        self.first().expect("No paths available").root_node()
    }

    fn get_block_number(&self) -> Result<BlockNumber, Error> {
        self.first().expect("No paths available").get_block_number()
    }
}

#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct LeafPathAndRoot<const L: usize, const M: usize, C: CurveTreeConfig> {
    pub leaf: CompressedLeafValue<C>,
    pub leaf_index: LeafIndex,
    pub path: WrappedCanonical<CurveTreePath<L, C>>,
    pub block_number: BlockNumber,
    pub root: Vec<u8>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> LeafPathAndRoot<L, M, C> {
    pub fn get_path(&self) -> Result<CurveTreePath<L, C>, Error> {
        self.path.decode()
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeLookup<L, M, C>
    for LeafPathAndRoot<L, M, C>
{
    fn get_path_to_leaf_index(&self, leaf_index: LeafIndex) -> Result<CurveTreePath<L, C>, Error> {
        if self.leaf_index == leaf_index {
            self.get_path()
        } else {
            Err(Error::LeafIndexNotFound(leaf_index))
        }
    }

    fn get_path_to_leaf(&self, leaf: CompressedLeafValue<C>) -> Result<CurveTreePath<L, C>, Error> {
        if self.leaf == leaf {
            self.get_path()
        } else {
            Err(Error::LeafNotFound)
        }
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        C::parameters()
    }

    fn root_node(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, Error> {
        // Decode the root from bytes
        let root = CompressedCurveTreeRoot::<L, M, C>::decode(&mut self.root.as_slice())
            .map_err(|_| Error::CurveTreeRootNotFound)?;
        Ok(root)
    }

    fn get_block_number(&self) -> Result<BlockNumber, Error> {
        Ok(self.block_number)
    }
}

pub trait CurveTreeBackend<const L: usize, const M: usize, C: CurveTreeConfig>: Sized {
    type Error: From<crate::Error>;
    type Updater: CurveTreeUpdater<L, M, C>;

    fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Self::Error>;

    fn parameters(&self) -> &SelRerandParameters<C::P0, C::P1>;

    fn get_block_number(&self) -> Result<BlockNumber, Self::Error>;

    fn set_block_number(&mut self, _block_number: BlockNumber) -> Result<(), Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn store_root(
        &mut self,
        _root: CompressedCurveTreeRoot<L, M, C>,
    ) -> Result<BlockNumber, Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn fetch_root(
        &self,
        block_number: BlockNumber,
    ) -> Result<CompressedCurveTreeRoot<L, M, C>, Self::Error>;

    fn height(&self) -> NodeLevel;

    fn set_height(&mut self, _height: NodeLevel) -> Result<(), Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn allocate_leaf_index(&mut self) -> LeafIndex;

    fn batch_inserts_supported(&self) -> bool {
        false
    }

    fn last_committed_leaf_index(&self) -> Result<LeafIndex, Self::Error> {
        Ok(0)
    }

    fn set_committed_leaf_index(&mut self, _leaf_index: LeafIndex) -> Result<(), Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn get_leaf(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<Option<CompressedLeafValue<C>>, Self::Error>;

    fn set_leaf(
        &mut self,
        _leaf_index: LeafIndex,
        _new_leaf_value: CompressedLeafValue<C>,
    ) -> Result<Option<CompressedLeafValue<C>>, Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }

    fn leaf_count(&self) -> LeafIndex;

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> Result<Option<CompressedInner<M, C>>, Self::Error>;

    fn set_inner_node(
        &mut self,
        _location: NodeLocation<L>,
        _new_node: CompressedInner<M, C>,
    ) -> Result<(), Self::Error> {
        Err(Error::CurveTreeBackendReadOnly.into())
    }
}

#[cfg(feature = "async_tree")]
pub trait AsyncCurveTreeBackend<const L: usize, const M: usize, C: CurveTreeConfig>: Sized {
    type Error: From<crate::Error>;
    type Updater: CurveTreeUpdater<L, M, C>;

    fn new(
        height: NodeLevel,
        gens_length: usize,
    ) -> impl Future<Output = Result<Self, Self::Error>> + Send;

    fn parameters(&self) -> impl Future<Output = &SelRerandParameters<C::P0, C::P1>> + Send;

    fn get_block_number(&self) -> impl Future<Output = Result<BlockNumber, Self::Error>> + Send;

    fn set_block_number(
        &mut self,
        _block_number: BlockNumber,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send {
        async move { Err(Error::CurveTreeBackendReadOnly.into()) }
    }

    fn store_root(
        &mut self,
        _root: CompressedCurveTreeRoot<L, M, C>,
    ) -> impl Future<Output = Result<BlockNumber, Self::Error>> + Send {
        async move { Err(Error::CurveTreeBackendReadOnly.into()) }
    }

    fn fetch_root(
        &self,
        block_number: BlockNumber,
    ) -> impl Future<Output = Result<CompressedCurveTreeRoot<L, M, C>, Self::Error>> + Send;

    fn height(&self) -> impl Future<Output = NodeLevel> + Send;

    fn set_height(
        &mut self,
        _height: NodeLevel,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send {
        async move { Err(Error::CurveTreeBackendReadOnly.into()) }
    }

    fn allocate_leaf_index(&mut self) -> impl Future<Output = LeafIndex> + Send;

    fn batch_inserts_supported(&self) -> bool {
        false
    }

    fn last_committed_leaf_index(
        &self,
    ) -> impl Future<Output = Result<LeafIndex, Self::Error>> + Send {
        async move { Ok(0) }
    }

    fn set_committed_leaf_index(
        &mut self,
        _leaf_index: LeafIndex,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send {
        async move { Err(Error::CurveTreeBackendReadOnly.into()) }
    }

    fn get_leaf(
        &self,
        leaf_index: LeafIndex,
    ) -> impl Future<Output = Result<Option<CompressedLeafValue<C>>, Self::Error>> + Send;

    fn set_leaf(
        &mut self,
        _leaf_index: LeafIndex,
        _new_leaf_value: CompressedLeafValue<C>,
    ) -> impl Future<Output = Result<Option<CompressedLeafValue<C>>, Self::Error>> + Send {
        async move { Err(Error::CurveTreeBackendReadOnly.into()) }
    }

    fn leaf_count(&self) -> impl Future<Output = LeafIndex> + Send;

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> impl Future<Output = Result<Option<CompressedInner<M, C>>, Self::Error>> + Send;

    fn set_inner_node(
        &mut self,
        _location: NodeLocation<L>,
        _new_node: CompressedInner<M, C>,
    ) -> impl Future<Output = Result<(), Self::Error>> + Send {
        async move { Err(Error::CurveTreeBackendReadOnly.into()) }
    }
}

pub struct CurveTreeMemoryBackend<const L: usize, const M: usize, C: CurveTreeConfig> {
    height: NodeLevel,
    leafs: Vec<CompressedLeafValue<C>>,
    next_leaf_index: LeafIndex,
    committed_leaf_index: LeafIndex,
    nodes: BTreeMap<NodeLocation<L>, CompressedInner<M, C>>,
    block_number: BlockNumber,
    roots: BTreeMap<BlockNumber, CompressedCurveTreeRoot<L, M, C>>,
    parameters: SelRerandParameters<C::P0, C::P1>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> core::fmt::Debug
    for CurveTreeMemoryBackend<L, M, C>
{
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.debug_struct("CurveTreeMemoryBackend")
            .field("height", &self.height)
            .field("leafs", &self.leafs)
            .field("next_leaf_index", &self.next_leaf_index)
            .field("committed_leaf_index", &self.committed_leaf_index)
            .field("nodes", &self.nodes)
            .field("block_number", &self.block_number)
            .finish()
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeMemoryBackend<L, M, C> {
    pub fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Error> {
        Ok(Self {
            height,
            leafs: Vec::new(),
            next_leaf_index: 0,
            committed_leaf_index: 0,
            nodes: BTreeMap::new(),
            block_number: 0,
            roots: BTreeMap::new(),
            parameters: SelRerandParameters::new(gens_length, gens_length)?,
        })
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeBackend<L, M, C>
    for CurveTreeMemoryBackend<L, M, C>
{
    type Error = Error;
    type Updater = DefaultCurveTreeUpdater<L, M, C>;

    fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Self::Error> {
        Ok(CurveTreeMemoryBackend::new(height, gens_length)?)
    }

    fn parameters(&self) -> &SelRerandParameters<C::P0, C::P1> {
        &self.parameters
    }

    fn get_block_number(&self) -> Result<BlockNumber, Self::Error> {
        Ok(self.block_number.into())
    }

    fn set_block_number(&mut self, block_number: BlockNumber) -> Result<(), Self::Error> {
        self.block_number = block_number
            .try_into()
            .expect("Block number conversion failed");
        Ok(())
    }

    fn store_root(
        &mut self,
        root: CompressedCurveTreeRoot<L, M, C>,
    ) -> Result<BlockNumber, Self::Error> {
        let block_number = self.block_number + 1;
        self.block_number = block_number;
        self.roots.insert(block_number, root);
        Ok(block_number.into())
    }

    fn fetch_root(
        &self,
        block_number: BlockNumber,
    ) -> Result<CompressedCurveTreeRoot<L, M, C>, Self::Error> {
        let block_number: BlockNumber = block_number
            .try_into()
            .expect("Block number conversion failed");
        self.roots
            .get(&block_number)
            .cloned()
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

    fn batch_inserts_supported(&self) -> bool {
        true
    }

    fn last_committed_leaf_index(&self) -> Result<LeafIndex, Self::Error> {
        Ok(self.committed_leaf_index)
    }

    fn set_committed_leaf_index(&mut self, leaf_index: LeafIndex) -> Result<(), Self::Error> {
        self.committed_leaf_index = leaf_index;
        Ok(())
    }

    fn get_leaf(&self, leaf_index: LeafIndex) -> Result<Option<CompressedLeafValue<C>>, Error> {
        Ok(self.leafs.get(leaf_index as usize).copied())
    }

    fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: CompressedLeafValue<C>,
    ) -> Result<Option<CompressedLeafValue<C>>, Error> {
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

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> Result<Option<CompressedInner<M, C>>, Error> {
        Ok(self.nodes.get(&location).cloned())
    }

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: CompressedInner<M, C>,
    ) -> Result<(), Error> {
        self.nodes.insert(location, new_node);
        Ok(())
    }
}

#[cfg(feature = "async_tree")]
impl<const L: usize, const M: usize, C: CurveTreeConfig> AsyncCurveTreeBackend<L, M, C>
    for CurveTreeMemoryBackend<L, M, C>
where
    Self: CurveTreeBackend<L, M, C, Error = Error>,
{
    type Error = Error;
    type Updater = DefaultCurveTreeUpdater<L, M, C>;

    async fn new(height: NodeLevel, gens_length: usize) -> Result<Self, Self::Error> {
        Ok(CurveTreeMemoryBackend::new(height, gens_length)?)
    }

    async fn parameters(&self) -> &SelRerandParameters<C::P0, C::P1> {
        &self.parameters
    }

    async fn get_block_number(&self) -> Result<BlockNumber, Self::Error> {
        Ok(self.block_number.into())
    }

    async fn set_block_number(&mut self, block_number: BlockNumber) -> Result<(), Self::Error> {
        self.block_number = block_number
            .try_into()
            .expect("Block number conversion failed");
        Ok(())
    }

    async fn store_root(
        &mut self,
        root: CompressedCurveTreeRoot<L, M, C>,
    ) -> Result<BlockNumber, Self::Error> {
        let block_number = self.block_number + 1;
        self.block_number = block_number;
        self.roots.insert(block_number, root);
        Ok(block_number.into())
    }

    async fn fetch_root(
        &self,
        block_number: BlockNumber,
    ) -> Result<CompressedCurveTreeRoot<L, M, C>, Self::Error> {
        let block_number: BlockNumber = block_number
            .try_into()
            .expect("Block number conversion failed");
        self.roots
            .get(&block_number)
            .cloned()
            .ok_or(Error::CurveTreeRootNotFound)
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

    async fn last_committed_leaf_index(&self) -> Result<LeafIndex, Self::Error> {
        CurveTreeBackend::last_committed_leaf_index(self)
    }

    async fn set_committed_leaf_index(&mut self, leaf_index: LeafIndex) -> Result<(), Self::Error> {
        CurveTreeBackend::set_committed_leaf_index(self, leaf_index)
    }

    async fn get_leaf(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<Option<CompressedLeafValue<C>>, Error> {
        CurveTreeBackend::get_leaf(self, leaf_index)
    }

    async fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: CompressedLeafValue<C>,
    ) -> Result<Option<CompressedLeafValue<C>>, Error> {
        CurveTreeBackend::set_leaf(self, leaf_index, new_leaf_value)
    }

    async fn leaf_count(&self) -> LeafIndex {
        CurveTreeBackend::leaf_count(self)
    }

    async fn get_inner_node(
        &self,
        location: NodeLocation<L>,
    ) -> Result<Option<CompressedInner<M, C>>, Error> {
        CurveTreeBackend::get_inner_node(self, location)
    }

    async fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: CompressedInner<M, C>,
    ) -> Result<(), Error> {
        CurveTreeBackend::set_inner_node(self, location, new_node)
    }
}
