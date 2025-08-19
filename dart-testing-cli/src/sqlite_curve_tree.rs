use anyhow::Result;
use codec::{Decode, Encode};
use core::ops::{Deref, DerefMut};
use rusqlite::Connection;
use std::sync::Arc;

use polymesh_dart::{
    curve_tree::{
        AccountTreeConfig, AssetTreeConfig, CurveTreeBackend, CurveTreeLookup, CurveTreeParameters,
        CurveTreePath, CurveTreeRoot, CurveTreeWithBackend, Inner, LeafValue, NodeLocation, Root,
        SelRerandParameters, ValidateCurveTreeRoot,
    },
    BlockNumber, Error as DartError, LeafIndex, NodeLevel, PallasParameters, VestaParameters,
    ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_L, ACCOUNT_TREE_M, ASSET_TREE_HEIGHT, ASSET_TREE_L,
    ASSET_TREE_M,
};

lazy_static::lazy_static! {
    static ref CURVE_TREE_PARAMETERS: CurveTreeParameters<AssetTreeConfig> = CurveTreeParameters::<AssetTreeConfig>::new(
        polymesh_dart::MAX_CURVE_TREE_GENS,
        polymesh_dart::MAX_CURVE_TREE_GENS,
    ).expect("Failed to create curve tree parameters");
}

/// Asset Curve Tree SQLite Storage backend.
#[derive(Clone)]
pub struct AssetCurveTreeSqliteStorage {
    db: Arc<Connection>,
}

impl AssetCurveTreeSqliteStorage {
    pub fn new(db: Arc<Connection>) -> Self {
        Self { db }
    }
}

impl CurveTreeBackend<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig> for AssetCurveTreeSqliteStorage {
    type Error = anyhow::Error;

    fn new(_height: NodeLevel, _gens_length: usize) -> Result<Self, Self::Error> {
        Err(anyhow::anyhow!(
            "AssetCurveTreeSqliteStorage does not support new() - use new() with db connection"
        ))
    }

    fn parameters(&self) -> &SelRerandParameters<PallasParameters, VestaParameters> {
        &CURVE_TREE_PARAMETERS
    }

    fn get_block_number(&self) -> Result<BlockNumber, Self::Error> {
        let mut stmt = self
            .db
            .prepare("SELECT MAX(block_number) FROM asset_root_history")?;
        let block_number: i64 = stmt.query_row([], |row| row.get(0))?;
        Ok(block_number as BlockNumber)
    }

    fn store_root(
        &mut self,
        root: Root<ASSET_TREE_L, ASSET_TREE_M, PallasParameters, VestaParameters>,
    ) -> std::result::Result<BlockNumber, Self::Error> {
        let block_number = self.get_block_number()? + 1;
        let root = CurveTreeRoot::<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>::new(&root)
            .map_err(|_| anyhow::anyhow!("Failed to create CurveTreeRoot from root data"))?;
        let root_bytes = root.encode();
        let mut stmt = self
            .db
            .prepare("INSERT INTO asset_root_history (block_number, root_data) VALUES (?1, ?2)")?;
        stmt.execute((block_number as i64, root_bytes))?;
        Ok(block_number)
    }

    fn fetch_root(
        &self,
        block_number: BlockNumber,
    ) -> std::result::Result<
        Root<ASSET_TREE_L, ASSET_TREE_M, PallasParameters, VestaParameters>,
        Self::Error,
    > {
        let mut stmt = self
            .db
            .prepare("SELECT root_data FROM asset_root_history WHERE block_number = ?1")?;
        let root_data: Vec<u8> = stmt.query_row([block_number as i64], |row| row.get(0))?;
        // The root was encoded as CurveTreeRoot, so decode it directly
        let root: CurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig> =
            Decode::decode(&mut root_data.as_slice())?;
        Ok(root.decode()?)
    }

    fn height(&self) -> NodeLevel {
        ASSET_TREE_HEIGHT
    }

    fn set_height(&mut self, _height: NodeLevel) -> Result<(), Self::Error> {
        Err(anyhow::anyhow!(
            "Read-only storage does not support set_height()"
        ))
    }

    fn allocate_leaf_index(&mut self) -> LeafIndex {
        let mut stmt = self
            .db
            .prepare("SELECT COALESCE(MAX(leaf_index), -1) + 1 FROM asset_leaves")
            .unwrap();
        let next_index: i64 = stmt.query_row([], |row| row.get(0)).unwrap_or(0);
        next_index as LeafIndex
    }

    fn get_leaf(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<Option<LeafValue<PallasParameters>>, Self::Error> {
        let mut stmt = self
            .db
            .prepare("SELECT leaf_data FROM asset_leaves WHERE leaf_index = ?1")?;
        let mut rows = stmt.query_map([leaf_index], |row| {
            let data: Vec<u8> = row.get(0)?;
            Ok(data)
        })?;

        if let Some(row) = rows.next() {
            let data = row?;
            let leaf = Decode::decode(&mut &data[..])?;
            Ok(Some(leaf))
        } else {
            Ok(None)
        }
    }

    fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: LeafValue<PallasParameters>,
    ) -> Result<Option<LeafValue<PallasParameters>>, Self::Error> {
        // Get the old leaf value if it exists
        let old_leaf = self.get_leaf(leaf_index)?;

        // Encode the new leaf value
        let leaf_data = new_leaf_value.encode();

        // Insert or update the leaf
        let mut stmt = self.db.prepare(
            "INSERT OR REPLACE INTO asset_leaves (leaf_index, leaf_data) VALUES (?1, ?2)",
        )?;
        stmt.execute((leaf_index, &leaf_data))?;

        Ok(old_leaf)
    }

    fn leaf_count(&self) -> LeafIndex {
        let mut stmt = self
            .db
            .prepare("SELECT COUNT(*) FROM asset_leaves")
            .unwrap();
        let count: i64 = stmt.query_row([], |row| row.get(0)).unwrap_or(0);
        count as LeafIndex
    }

    fn get_inner_node(
        &self,
        location: NodeLocation<ASSET_TREE_L>,
    ) -> Result<Option<Inner<1, AssetTreeConfig>>, Self::Error> {
        let mut stmt = self
            .db
            .prepare("SELECT node_data FROM asset_inner_nodes WHERE location = ?1")?;
        let location_bytes = location.encode();
        let mut rows = stmt.query_map([location_bytes], |row| {
            let data: Vec<u8> = row.get(0)?;
            Ok(data)
        })?;

        if let Some(row) = rows.next() {
            let data = row?;
            let node = Decode::decode(&mut &data[..])?;
            Ok(Some(node))
        } else {
            Ok(None)
        }
    }

    fn set_inner_node(
        &mut self,
        location: NodeLocation<ASSET_TREE_L>,
        new_node: Inner<1, AssetTreeConfig>,
    ) -> Result<(), Self::Error> {
        // Encode the location and node data
        let location_bytes = location.encode();
        let node_data = new_node.encode();

        // Insert or update the inner node
        let mut stmt = self.db.prepare(
            "INSERT OR REPLACE INTO asset_inner_nodes (location, node_data) VALUES (?1, ?2)",
        )?;
        stmt.execute((location_bytes, node_data))?;

        Ok(())
    }
}

pub type AssetCurveTreeType = CurveTreeWithBackend<
    ASSET_TREE_L,
    1,
    AssetTreeConfig,
    AssetCurveTreeSqliteStorage,
    anyhow::Error,
>;

#[derive(Clone)]
pub struct AssetCurveTree(pub AssetCurveTreeType);

impl Deref for AssetCurveTree {
    type Target = AssetCurveTreeType;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for AssetCurveTree {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl AssetCurveTree {
    pub fn new(db: Arc<Connection>) -> Result<Self> {
        let backend = AssetCurveTreeSqliteStorage::new(db);
        Ok(Self(CurveTreeWithBackend::new_with_backend(backend)?))
    }
}

/// Account Curve Tree SQLite Storage backend.
#[derive(Clone)]
pub struct AccountCurveTreeSqliteStorage {
    db: Arc<Connection>,
}

impl AccountCurveTreeSqliteStorage {
    pub fn new(db: Arc<Connection>) -> Self {
        Self { db }
    }

    pub fn find_leaf_index(&self, leaf: &LeafValue<PallasParameters>) -> Result<Option<LeafIndex>> {
        let mut stmt = self
            .db
            .prepare("SELECT leaf_index FROM account_leaves WHERE leaf_data = ?1")?;
        let leaf_data = leaf.encode();
        let mut rows = stmt.query_map([leaf_data], |row| row.get(0))?;

        if let Some(row) = rows.next() {
            Ok(Some(row?))
        } else {
            Ok(None)
        }
    }
}

impl CurveTreeBackend<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>
    for AccountCurveTreeSqliteStorage
{
    type Error = anyhow::Error;

    fn new(_height: NodeLevel, _gens_length: usize) -> Result<Self, Self::Error> {
        Err(anyhow::anyhow!(
            "AccountCurveTreeSqliteStorage does not support new() - use new() with db connection"
        ))
    }

    fn parameters(&self) -> &SelRerandParameters<PallasParameters, VestaParameters> {
        &CURVE_TREE_PARAMETERS
    }

    fn get_block_number(&self) -> Result<BlockNumber, Self::Error> {
        let mut stmt = self
            .db
            .prepare("SELECT MAX(block_number) FROM account_root_history")?;
        let block_number: i64 = stmt.query_row([], |row| row.get(0))?;
        Ok(block_number as BlockNumber)
    }

    fn store_root(
        &mut self,
        root: Root<ACCOUNT_TREE_L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>,
    ) -> std::result::Result<BlockNumber, Self::Error> {
        let block_number = self.get_block_number()? + 1;
        let root = CurveTreeRoot::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(&root)
            .map_err(|_| anyhow::anyhow!("Failed to create CurveTreeRoot from root data"))?;
        let root_bytes = root.encode();
        let mut stmt = self.db.prepare(
            "INSERT INTO account_root_history (block_number, root_data) VALUES (?1, ?2)",
        )?;
        stmt.execute((block_number as i64, root_bytes))?;
        Ok(block_number)
    }

    fn fetch_root(
        &self,
        block_number: BlockNumber,
    ) -> std::result::Result<
        Root<ACCOUNT_TREE_L, ACCOUNT_TREE_M, PallasParameters, VestaParameters>,
        Self::Error,
    > {
        let mut stmt = self
            .db
            .prepare("SELECT root_data FROM account_root_history WHERE block_number = ?1")?;
        let root_data: Vec<u8> = stmt.query_row([block_number as i64], |row| row.get(0))?;
        // The root was encoded as CurveTreeRoot, so decode it directly
        let root: CurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig> =
            Decode::decode(&mut root_data.as_slice())?;
        Ok(root.decode()?)
    }

    fn height(&self) -> NodeLevel {
        ACCOUNT_TREE_HEIGHT
    }

    fn set_height(&mut self, _height: NodeLevel) -> Result<(), Self::Error> {
        Err(anyhow::anyhow!(
            "Read-only storage does not support set_height()"
        ))
    }

    fn allocate_leaf_index(&mut self) -> LeafIndex {
        let mut stmt = self
            .db
            .prepare("SELECT COALESCE(MAX(leaf_index), -1) + 1 FROM account_leaves")
            .unwrap();
        let next_index: i64 = stmt.query_row([], |row| row.get(0)).unwrap_or(0);
        next_index as LeafIndex
    }

    fn get_leaf(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<Option<LeafValue<PallasParameters>>, Self::Error> {
        let mut stmt = self
            .db
            .prepare("SELECT leaf_data FROM account_leaves WHERE leaf_index = ?1")?;
        let mut rows = stmt.query_map([leaf_index], |row| {
            let data: Vec<u8> = row.get(0)?;
            Ok(data)
        })?;

        if let Some(row) = rows.next() {
            let data = row?;
            let leaf = Decode::decode(&mut &data[..])?;
            Ok(Some(leaf))
        } else {
            Ok(None)
        }
    }

    fn set_leaf(
        &mut self,
        leaf_index: LeafIndex,
        new_leaf_value: LeafValue<PallasParameters>,
    ) -> Result<Option<LeafValue<PallasParameters>>, Self::Error> {
        // Get the old leaf value if it exists
        let old_leaf = self.get_leaf(leaf_index)?;

        // Encode the new leaf value
        let leaf_data = new_leaf_value.encode();

        // Insert or update the leaf
        let mut stmt = self.db.prepare(
            "INSERT OR REPLACE INTO account_leaves (leaf_index, leaf_data) VALUES (?1, ?2)",
        )?;
        stmt.execute((leaf_index, &leaf_data))?;

        Ok(old_leaf)
    }

    fn leaf_count(&self) -> LeafIndex {
        let mut stmt = self
            .db
            .prepare("SELECT COUNT(*) FROM account_leaves")
            .unwrap();
        let count: i64 = stmt.query_row([], |row| row.get(0)).unwrap_or(0);
        count as LeafIndex
    }

    fn get_inner_node(
        &self,
        location: NodeLocation<ACCOUNT_TREE_L>,
    ) -> Result<Option<Inner<1, AccountTreeConfig>>, Self::Error> {
        let mut stmt = self
            .db
            .prepare("SELECT node_data FROM account_inner_nodes WHERE location = ?1")?;
        let location_bytes = location.encode();
        let mut rows = stmt.query_map([location_bytes], |row| {
            let data: Vec<u8> = row.get(0)?;
            Ok(data)
        })?;

        if let Some(row) = rows.next() {
            let data = row?;
            let node = Decode::decode(&mut &data[..])?;
            Ok(Some(node))
        } else {
            Ok(None)
        }
    }

    fn set_inner_node(
        &mut self,
        location: NodeLocation<ACCOUNT_TREE_L>,
        new_node: Inner<1, AccountTreeConfig>,
    ) -> Result<(), Self::Error> {
        // Encode the location and node data
        let location_bytes = location.encode();
        let node_data = new_node.encode();

        // Insert or update the inner node
        let mut stmt = self.db.prepare(
            "INSERT OR REPLACE INTO account_inner_nodes (location, node_data) VALUES (?1, ?2)",
        )?;
        stmt.execute((location_bytes, node_data))?;

        Ok(())
    }
}

pub type AccountCurveTreeType = CurveTreeWithBackend<
    ACCOUNT_TREE_L,
    1,
    AccountTreeConfig,
    AccountCurveTreeSqliteStorage,
    anyhow::Error,
>;

#[derive(Clone)]
pub struct AccountCurveTree(pub AccountCurveTreeType);

impl Deref for AccountCurveTree {
    type Target = AccountCurveTreeType;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for AccountCurveTree {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl AccountCurveTree {
    pub fn new(db: Arc<Connection>) -> Result<Self> {
        let backend = AccountCurveTreeSqliteStorage::new(db);
        Ok(Self(CurveTreeWithBackend::new_with_backend(backend)?))
    }
}

impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig> for &AccountCurveTree {
    fn get_path_to_leaf_index(
        &self,
        leaf_index: LeafIndex,
    ) -> Result<CurveTreePath<ACCOUNT_TREE_L, AccountTreeConfig>, DartError> {
        Ok(self
            .0
            .get_path_to_leaf(leaf_index, 0)
            .map_err(|_| DartError::LeafIndexNotFound(leaf_index))?)
    }

    fn get_path_to_leaf(
        &self,
        leaf: LeafValue<PallasParameters>,
    ) -> Result<CurveTreePath<ACCOUNT_TREE_L, AccountTreeConfig>, DartError> {
        let leaf_index = self.0.backend.find_leaf_index(&leaf).map_err(|er| {
            log::error!("Error finding leaf index: {:?}", er);
            DartError::LeafNotFound
        })?;

        if let Some(index) = leaf_index {
            self.get_path_to_leaf_index(index)
        } else {
            Err(DartError::LeafNotFound)
        }
    }

    fn params(&self) -> &CurveTreeParameters<AccountTreeConfig> {
        &CURVE_TREE_PARAMETERS
    }

    fn root_node(
        &self,
    ) -> Result<CurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>, DartError> {
        let root = self
            .0
            .root_node()
            .map_err(|_| DartError::CurveTreeRootNotFound)?;
        Ok(CurveTreeRoot::new(&root)?)
    }

    fn get_block_number(&self) -> Result<BlockNumber, DartError> {
        self.0
            .get_block_number()
            .map_err(|_| DartError::CurveTreeBlockNumberNotFound)
    }
}

/// Asset Curve Tree Root History SQLite Storage.
#[derive(Clone)]
pub struct AssetRootHistory {
    db: Arc<Connection>,
}

impl AssetRootHistory {
    pub fn new(db: Arc<Connection>) -> Self {
        Self { db }
    }

    pub fn add_root(
        &mut self,
        block: BlockNumber,
        root: &CurveTreeRoot<ASSET_TREE_L, ACCOUNT_TREE_M, AssetTreeConfig>,
    ) -> Result<()> {
        let root_bytes = root.encode();
        let mut stmt = self
            .db
            .prepare("INSERT INTO asset_root_history (block_number, root_data) VALUES (?1, ?2)")?;
        stmt.execute((block as i64, root_bytes))?;
        Ok(())
    }
}

impl ValidateCurveTreeRoot<ASSET_TREE_L, ACCOUNT_TREE_M, AssetTreeConfig> for &AssetRootHistory {
    fn get_block_root(
        &self,
        block: BlockNumber,
    ) -> Option<CurveTreeRoot<ASSET_TREE_L, ACCOUNT_TREE_M, AssetTreeConfig>> {
        let mut stmt = self
            .db
            .prepare("SELECT root_data FROM asset_root_history WHERE block_number = ?1")
            .ok()?;
        let root_data: Vec<u8> = stmt.query_row([block as i64], |row| row.get(0)).ok()?;
        // The root was encoded as CurveTreeRoot, so decode it directly
        Decode::decode(&mut root_data.as_slice()).ok()
    }

    fn params(&self) -> &CurveTreeParameters<AssetTreeConfig> {
        &CURVE_TREE_PARAMETERS
    }
}

/// Account Curve Tree Root History SQLite Storage.
#[derive(Clone)]
pub struct AccountRootHistory {
    db: Arc<Connection>,
}

impl AccountRootHistory {
    pub fn new(db: Arc<Connection>) -> Self {
        Self { db }
    }

    pub fn add_root(
        &mut self,
        block: BlockNumber,
        root: &CurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    ) -> Result<()> {
        let root_bytes = root.encode();
        let mut stmt = self.db.prepare(
            "INSERT INTO account_root_history (block_number, root_data) VALUES (?1, ?2)",
        )?;
        stmt.execute((block as i64, root_bytes))?;
        Ok(())
    }
}

impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>
    for &AccountRootHistory
{
    fn get_block_root(
        &self,
        block: BlockNumber,
    ) -> Option<CurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>> {
        let mut stmt = self
            .db
            .prepare("SELECT root_data FROM account_root_history WHERE block_number = ?1")
            .ok()?;
        let root_data: Vec<u8> = stmt.query_row([block as i64], |row| row.get(0)).ok()?;
        // The root was encoded as CurveTreeRoot, so decode it directly
        Decode::decode(&mut root_data.as_slice()).ok()
    }

    fn params(&self) -> &CurveTreeParameters<AccountTreeConfig> {
        &CURVE_TREE_PARAMETERS
    }
}
