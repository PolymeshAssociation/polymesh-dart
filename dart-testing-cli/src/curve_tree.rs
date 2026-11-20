//! SQLite curve tree backends that mirror the pallet's storage backends
//! (`Polymesh/pallets/confidential-assets/src/curve_tree.rs`).
//!
//! Parity points the previous CLI backend did not model:
//! - one chain-wide block number (`frame_system`), not a per-tree counter;
//! - roots are keyed by `(tree, block)` and replaced within a block, mirroring
//!   `store_*_curve_tree_root` on a `StorageMap` (`INSERT OR REPLACE`);
//! - `height(block)` returns the *current* height for any block, as the pallet's backends do;
//! - `set_height` actually persists the height (`*CurveTreeHeight`);
//! - the account and fee trees support batched inserts: a leaf is written during the extrinsic and
//!   the root is only recomputed at block finalization, so a proof in the same block cannot see it;
//! - `fetch_root` applies the maximum root age check, so an expired root fails verification with
//!   `CurveTreeRootNotFound`.

use codec::{Decode, Encode};
use core::marker::PhantomData;
use std::sync::Arc;

use polymesh_dart::curve_tree::{
    AccountTreeConfig, AssetTreeConfig, CompressedCurveTreeRoot, CompressedInner,
    CompressedLeafValue, CurveTreeBackend, CurveTreeConfig, CurveTreeLookup, CurveTreeParameters,
    CurveTreePath, CurveTreeWithBackend, DefaultCurveTreeUpdater, FeeAccountTreeConfig,
    NodeLocation, ValidateCurveTreeRoot,
};
use polymesh_dart::{
    BlockNumber, Error as DartError, LeafIndex, NodeLevel, ACCOUNT_TREE_L, ACCOUNT_TREE_M,
    ASSET_TREE_L, ASSET_TREE_M, FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M,
};

use crate::config::TreeKind;
use crate::errors::{ChainError, ChainFailure, ChainResult};
use crate::storage::Store;

pub type AssetTree = Tree<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>;
pub type AccountTree = Tree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>;
pub type FeeAccountTree = Tree<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>;

pub type Tree<const L: usize, const M: usize, C> =
    CurveTreeWithBackend<L, M, C, StoreBackend<L, M, C>, ChainFailure>;

/// SQLite-backed curve tree storage, mirroring the pallet's `*CurveTreeStorage` backends.
pub struct StoreBackend<const L: usize, const M: usize, C: CurveTreeConfig> {
    pub store: Arc<Store>,
    pub tree: TreeKind,
    _marker: PhantomData<C>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> Clone for StoreBackend<L, M, C> {
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
            tree: self.tree,
            _marker: PhantomData,
        }
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> StoreBackend<L, M, C> {
    /// A DB-backed backend cannot be built from a height alone, so the trait's `new()` is not usable
    /// here; this is the constructor the CLI uses.
    pub fn new(store: Arc<Store>, tree: TreeKind) -> Self {
        Self {
            store,
            tree,
            _marker: PhantomData,
        }
    }

    /// `AccountTreeConfig::APPEND_ONLY` / `FeeAccountTreeConfig::APPEND_ONLY` — true for the trees
    /// the pallet treats as append-only, which are also the ones with batched inserts.
    fn append_only(&self) -> bool {
        C::APPEND_ONLY
    }

    /// Needed by the prover side to turn a state commitment into a path.
    pub fn find_leaf_index(&self, leaf: &CompressedLeafValue<C>) -> ChainResult<Option<LeafIndex>> {
        self.store.find_leaf_index(self.tree, &leaf.encode())
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeBackend<L, M, C>
    for StoreBackend<L, M, C>
{
    type Error = ChainFailure;
    type Updater = DefaultCurveTreeUpdater<L, M, C>;

    fn new(_height: NodeLevel) -> ChainResult<Self> {
        Err(ChainFailure::Internal(
            "StoreBackend needs a Store: use StoreBackend::new(store, tree)".into(),
        ))
    }

    fn parameters(&self) -> &CurveTreeParameters<C> {
        C::parameters()
    }

    /// `frame_system::Pallet::<T>::block_number()` — one chain-wide block shared by all trees.
    ///
    /// For the *prover* side of the CLI (proof generation), the tree's notion of "now" is the
    /// block of the last stored root — the same root a real client sees on the node. The
    /// raw chain block stays available via `Store::block_number` for the dispatch side.
    fn get_block_number(&self) -> ChainResult<BlockNumber> {
        match self.store.last_root_block(self.tree)? {
            Some(block) => Ok(block),
            None => self.store.block_number(),
        }
    }

    /// `<Tree>CurveTreeCurrentRoot`
    fn current_root(&self) -> ChainResult<CompressedCurveTreeRoot<L, M, C>> {
        let root = self
            .store
            .current_root(self.tree)?
            .ok_or(ChainFailure::Error(ChainError::CurveTreeRootNotFound))?;
        CompressedCurveTreeRoot::<L, M, C>::decode(&mut root.as_slice()).map_err(ChainFailure::from)
    }

    /// `store_*_curve_tree_root`: one row per `(tree, block)`, replaced within a block.
    fn store_root(&mut self, root: CompressedCurveTreeRoot<L, M, C>) -> ChainResult<BlockNumber> {
        let block = self.store.block_number()?;
        let moment = self.store.timestamp()?;
        self.store
            .store_root(self.tree, block, root.height, moment, &root.encode())?;
        Ok(block)
    }

    /// `get_*_curve_tree_root`, including the maximum root age check.
    fn fetch_root(
        &self,
        block_number: Option<BlockNumber>,
    ) -> ChainResult<CompressedCurveTreeRoot<L, M, C>> {
        let block = match block_number {
            Some(b) => b,
            None => self.store.block_number()?,
        };
        let root = self
            .store
            .get_block_root(self.tree, block)?
            .ok_or(ChainFailure::Error(ChainError::CurveTreeRootNotFound))?;
        CompressedCurveTreeRoot::<L, M, C>::decode(&mut root.as_slice()).map_err(ChainFailure::from)
    }

    /// `<Tree>CurveTreeHeight` — the pallet reports the current height for every block.
    fn height(&self, _block_number: Option<BlockNumber>) -> ChainResult<NodeLevel> {
        self.store.tree_height(self.tree)
    }

    fn set_height(&mut self, height: NodeLevel) -> ChainResult<()> {
        self.store.set_tree_height(self.tree, height)?;
        Ok(())
    }

    /// Asset leaves come from a `CountedStorageMap`; the account and fee trees use a
    /// `Next*LeafIndex` counter that is incremented on allocation.
    fn allocate_leaf_index(&mut self) -> LeafIndex {
        // The trait's signature cannot return an error, so a storage failure is logged and falls
        // back to an index that will fail verification.
        if self.append_only() {
            let index = match self.store.next_leaf_index(self.tree) {
                Ok(index) => index,
                Err(e) => {
                    log::error!("next leaf index: {e}");
                    return 0;
                }
            };
            if let Err(e) = self.store.set_next_leaf_index(self.tree, index + 1) {
                log::error!("set next leaf index: {e}");
            }
            index
        } else {
            match self.store.leaf_count(self.tree) {
                Ok(count) => count,
                Err(e) => {
                    log::error!("leaf count: {e}");
                    0
                }
            }
        }
    }

    fn batch_inserts_supported(&self) -> bool {
        self.append_only()
    }

    /// `LastCommitted*LeafIndex`
    fn last_committed_leaf_index(&self) -> ChainResult<LeafIndex> {
        self.store.last_committed_leaf_index(self.tree)
    }

    fn set_committed_leaf_index(&mut self, leaf_index: LeafIndex) -> ChainResult<()> {
        self.store
            .set_last_committed_leaf_index(self.tree, leaf_index)?;
        Ok(())
    }

    fn get_leaf(
        &self,
        leaf_index: LeafIndex,
        _block_number: Option<BlockNumber>,
    ) -> ChainResult<Option<CompressedLeafValue<C>>> {
        match self.store.get_leaf(self.tree, leaf_index)? {
            Some(leaf) => CompressedLeafValue::<C>::decode(&mut leaf.as_slice())
                .map(Some)
                .map_err(ChainFailure::from),
            None => Ok(None),
        }
    }

    fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: CompressedLeafValue<C>,
    ) -> ChainResult<Option<CompressedLeafValue<C>>> {
        let old = self.store.set_leaf(
            self.tree,
            leaf_index,
            &new_leaf_value.encode(),
            self.append_only(),
        )?;
        match (old, self.append_only()) {
            // The pallet's append-only backend always reports no previous value.
            (_, true) => Ok(None),
            (Some(old), false) => CompressedLeafValue::<C>::decode(&mut old.as_slice())
                .map(Some)
                .map_err(ChainFailure::from),
            (None, false) => Ok(None),
        }
    }

    fn leaf_count(&self) -> LeafIndex {
        if self.append_only() {
            self.store.next_leaf_index(self.tree).unwrap_or(0)
        } else {
            self.store.leaf_count(self.tree).unwrap_or(0)
        }
    }

    fn get_inner_node(
        &self,
        location: NodeLocation<L>,
        _block_number: Option<BlockNumber>,
    ) -> ChainResult<Option<CompressedInner<M, C>>> {
        match self.store.get_inner_node(self.tree, &location.encode())? {
            Some(node) => CompressedInner::<M, C>::decode(&mut node.as_slice())
                .map(Some)
                .map_err(ChainFailure::from),
            None => Ok(None),
        }
    }

    fn set_inner_node(
        &mut self,
        location: NodeLocation<L>,
        new_node: CompressedInner<M, C>,
    ) -> ChainResult<()> {
        self.store
            .set_inner_node(self.tree, &location.encode(), &new_node.encode())?;
        Ok(())
    }
}

/// A tree handle usable as proof context: `CurveTreeLookup` for paths and `ValidateCurveTreeRoot`
/// for the age-checked root lookup. `ChainFailure` is kept for the chain-facing calls; the lookup
/// trait's error type is fixed to `DartError`, so storage failures are mapped to the nearest
/// `DartError` variant and logged.
pub struct ChainTree<const L: usize, const M: usize, C: CurveTreeConfig> {
    pub tree: Tree<L, M, C>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> Clone for ChainTree<L, M, C> {
    fn clone(&self) -> Self {
        Self {
            tree: self.tree.clone(),
        }
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> ChainTree<L, M, C> {
    pub fn new(store: Arc<Store>, tree: TreeKind) -> ChainResult<Self> {
        let backend = StoreBackend::new(store, tree);
        let mut handle = Self {
            tree: Tree::new_with_backend(backend)?,
        };
        // Initialise the genesis root for the current block, like `get_*_curve_tree()` does.
        handle.tree.init_root()?;
        Ok(handle)
    }

    pub fn backend(&self) -> &StoreBackend<L, M, C> {
        &self.tree.backend
    }

    pub fn store(&self) -> &Arc<Store> {
        &self.tree.backend.store
    }

    pub fn kind(&self) -> TreeKind {
        self.tree.backend.tree
    }

    /// Block finalization: commit pending leaves and store the root for the current block.
    /// Mirrors `update_*_curve_tree_root`, which the pallet only runs for batch-insert trees.
    pub fn commit_pending_leaves(&mut self) -> ChainResult<bool> {
        // `commit_leaves_to_tree` stores the recomputed root for the current block.
        self.tree.commit_leaves_to_tree()
    }

    /// `curve_tree_min_update`: refresh the root timestamp when the minimum update interval has
    /// elapsed since the last update (`CurveTreeTimestamp::needs_update`).
    pub fn min_update(&mut self) -> ChainResult<()> {
        let now = self.store().timestamp()?;
        let last_update = self.store().last_update(self.kind())?;
        if now.saturating_sub(last_update) < self.store().config.min_curve_tree_root_update_interval
        {
            return Ok(());
        }
        let root = self.tree.root()?;
        self.tree.backend.store_root(root)?;
        Ok(())
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> CurveTreeLookup<L, M, C>
    for ChainTree<L, M, C>
{
    fn get_path_to_leaf_index(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<CurveTreePath<L, C>, DartError> {
        match self.tree.get_path_to_leaf_index(leaf_index) {
            Ok(path) => Ok(path),
            Err(e) => {
                log::error!("curve tree path lookup failed: {e}");
                Err(DartError::LeafIndexNotFound(leaf_index))
            }
        }
    }

    fn get_path_to_leaf(
        &self,
        leaf: CompressedLeafValue<C>,
    ) -> Result<CurveTreePath<L, C>, DartError> {
        match self.backend().find_leaf_index(&leaf) {
            Ok(Some(index)) => self.get_path_to_leaf_index(index),
            Ok(None) => Err(DartError::LeafNotFound),
            Err(e) => {
                log::error!("leaf lookup failed: {e}");
                Err(DartError::LeafNotFound)
            }
        }
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        C::parameters()
    }

    fn root(&self) -> Result<CompressedCurveTreeRoot<L, M, C>, DartError> {
        self.tree
            .root()
            .map_err(|_| DartError::CurveTreeRootNotFound)
    }

    fn get_block_number(&self) -> Result<BlockNumber, DartError> {
        self.tree
            .get_block_number()
            .map_err(|_| DartError::CurveTreeBlockNumberNotFound)
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> ValidateCurveTreeRoot<L, M, C>
    for ChainTree<L, M, C>
{
    fn get_block_root(&self, block: BlockNumber) -> Option<CompressedCurveTreeRoot<L, M, C>> {
        self.tree.get_block_root(block)
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        C::parameters()
    }
}
