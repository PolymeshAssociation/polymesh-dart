//! SQLite schema and typed accessors that mirror the Confidential Assets pallet storage.
//!
//! Each table below corresponds to one pallet storage item (see the `pallet::storage` section of
//! `Polymesh/pallets/confidential-assets/src/lib.rs`). Values are stored SCALE-encoded exactly as
//! the pallet stores them, so a reviewer can compare the CLI's state with a real chain's state.
//!
//! Two tables have no pallet equivalent and are explicitly marked as *prover state*: the CLI has to
//! remember the private state a prover used in order to build the next proof. On-chain, the chain
//! only keeps the leaf commitment and the nullifier.

use codec::{Decode, Encode};
use rusqlite::{params, Connection, OptionalExtension};
use std::cell::{Cell, RefCell};
use std::path::Path;
use std::sync::Arc;

use polymesh_dart::{
    AccountAssetState, AccountKeys, AccountPublicKey, AccountPublicKeys, AssetId, AssetKeys,
    EncryptionPublicKey, FeeAccountAssetState, LegEncrypted, LegId, SettlementRef,
};

use crate::config::{Moment, TestConfig, TreeKind};
use crate::errors::{ChainError, ChainFailure, ChainResult};

pub type Did = [u8; 32];
pub type BlockNumber = u32;

/// SQLite schema version. Bump this when the schema changes and add a step to
/// `Store::migrate`; recording-session databases from an older release can then be opened by a
/// newer CLI (the upgrade-simulation path).
pub const SCHEMA_VERSION: u32 = 1;

/// `Details` (pallet) — asset metadata plus the running total supply.
#[derive(Debug, Clone)]
pub struct AssetDetails {
    pub name: String,
    pub symbol: String,
    pub decimals: u8,
    pub issuer_identity_id: i64,
    pub total_supply: u64,
}

/// A confidential account: the CLI keeps the key seed so it can rebuild the prover's `AccountKeys`.
#[derive(Debug, Clone)]
pub struct AccountRow {
    pub id: i64,
    pub identity_id: i64,
    pub name: String,
    pub key_seed: String,
    pub public_keys: AccountPublicKeys,
}

impl AccountRow {
    pub fn account_keys(&self) -> ChainResult<AccountKeys> {
        AccountKeys::from_seed(&self.key_seed).map_err(ChainFailure::from)
    }
}

fn to_account_row(
    (id, identity_id, name, key_seed, acct, enc): (i64, i64, String, String, Vec<u8>, Vec<u8>),
) -> ChainResult<AccountRow> {
    Ok(AccountRow {
        id,
        identity_id,
        name,
        key_seed,
        public_keys: AccountPublicKeys {
            acct: AccountPublicKey::decode(&mut acct.as_slice())?,
            enc: EncryptionPublicKey::decode(&mut enc.as_slice())?,
        },
    })
}

/// Storage for the whole simulated chain. Shared by the curve tree backends and the extrinsics.
pub struct Store {
    pub conn: Arc<Connection>,
    pub config: TestConfig,
    /// Events buffered for the dispatch in progress; see `trace.rs`.
    pub pending_events: RefCell<Vec<(String, String)>>,
    /// Nesting depth of the simulated storage transactions (see `begin_tx`).
    tx_depth: Cell<usize>,
}

// SQLite integers are i64; every on-chain numeric type is unsigned. Reject values that do not fit
// rather than silently wrapping, mirroring the pallet's `amount_to_balance` overflow checks.
fn to_i64(v: u64) -> ChainResult<i64> {
    i64::try_from(v).map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))
}

fn from_i64(v: i64) -> ChainResult<u64> {
    u64::try_from(v).map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))
}

fn u32_from_i64(v: i64) -> ChainResult<u32> {
    u32::try_from(v).map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))
}

fn u8_from_i64(v: i64) -> ChainResult<u8> {
    u8::try_from(v).map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))
}

pub fn signer_to_did(signer_name: &str) -> ChainResult<Did> {
    let bytes = signer_name.as_bytes();
    // Polymesh DIDs are 32-byte identities; the CLI derives them from the signer name. Names longer
    // than a DID are rejected rather than truncated.
    if bytes.len() > 32 {
        return Err(ChainFailure::Error(ChainError::NameTooLong));
    }
    let mut did = [0u8; 32];
    did[..bytes.len()].copy_from_slice(bytes);
    Ok(did)
}

impl Store {
    pub fn connect<P: AsRef<Path>>(path: P, config: TestConfig) -> ChainResult<Self> {
        let conn = Arc::new(Connection::open(path)?);
        let store = Self {
            conn,
            config,
            pending_events: RefCell::new(Vec::new()),
            tx_depth: Cell::new(0),
        };
        store.create_schema()?;
        store.ensure_schema_version()?;
        Ok(store)
    }

    /// Check (and, for older databases, migrate) the SQLite schema version. A recording-session
    /// database written by an older CLI has an older version; `migrate` must bring it up to
    /// `SCHEMA_VERSION` before it is used.
    fn ensure_schema_version(&self) -> ChainResult<()> {
        match self.config_value("schema_version")? {
            None => {
                // A database created before the version marker existed, or a fresh one.
                self.set_config_value("schema_version", &SCHEMA_VERSION.to_string())?;
                Ok(())
            }
            Some(value) => {
                let version: u32 = value.parse().map_err(|_| {
                    ChainFailure::Internal(format!("invalid schema_version {value:?}"))
                })?;
                if version > SCHEMA_VERSION {
                    return Err(ChainFailure::Internal(format!(
                        "database schema v{version} is newer than this CLI (v{SCHEMA_VERSION})"
                    )));
                }
                self.migrate(version)
            }
        }
    }

    /// Schema migrations. Recording-session snapshots are the upgrade-test input, so each
    /// release that changes the schema adds a step here and bumps `SCHEMA_VERSION`.
    fn migrate(&self, from: u32) -> ChainResult<()> {
        if from < SCHEMA_VERSION {
            // No migrations yet. Future steps go here, e.g.:
            // if from < 2 { self.conn.execute("ALTER TABLE ...", [])?; }
            self.set_config_value("schema_version", &SCHEMA_VERSION.to_string())?;
        }
        Ok(())
    }

    pub fn initialize(&self) -> ChainResult<()> {
        // Reset atomically: a failure must not leave a half-initialized chain behind.
        self.begin_tx()?;
        let result = (|| -> ChainResult<()> {
            self.drop_schema()?;
            self.create_schema()?;
            // Genesis: block 1 with the pallet's genesis tree heights.
            self.conn.execute(
                "INSERT INTO chain_state (id, block_number, moment) VALUES (1, 1, 0)",
                [],
            )?;
            for tree in [TreeKind::Asset, TreeKind::Account, TreeKind::FeeAccount] {
                self.conn.execute(
                    "INSERT INTO tree_state (tree, height, next_leaf_index, last_committed_leaf_index, last_pruned_block, last_update_moment, current_root) VALUES (?1, ?2, 0, 0, 0, 0, NULL)",
                    params![tree.name(), self.config.genesis_height(tree) as i64],
                )?;
            }
            // Fee pool (`pallet_fee_id` account balance) starts empty.
            self.conn
                .execute("INSERT INTO fee_pool (id, balance) VALUES (1, 0)", [])?;
            self.set_config_value("schema_version", &SCHEMA_VERSION.to_string())?;
            Ok(())
        })();
        match result {
            Ok(()) => self.commit_tx(),
            Err(e) => {
                self.rollback_tx()?;
                Err(e)
            }
        }
    }

    pub fn drop_schema(&self) -> ChainResult<()> {
        for table in SCHEMA_TABLES {
            self.conn
                .execute(&format!("DROP TABLE IF EXISTS {table}"), [])?;
        }
        Ok(())
    }

    pub fn create_schema(&self) -> ChainResult<()> {
        self.conn.execute_batch(SCHEMA)?;
        Ok(())
    }

    // ---------------------------------------------------------------- simulated storage transactions
    //
    // Mirrors the pallet's storage-transaction semantics: every extrinsic body runs inside a
    // transaction that commits on `Ok` and rolls back on any `DispatchError`, so a failed check
    // leaves no state behind. Nested calls (batched extrinsics) use savepoints.

    pub fn begin_tx(&self) -> ChainResult<()> {
        let depth = self.tx_depth.get();
        if depth == 0 {
            self.conn.execute("BEGIN IMMEDIATE", [])?;
        } else {
            self.conn.execute(&format!("SAVEPOINT sp{depth}"), [])?;
        }
        self.tx_depth.set(depth + 1);
        Ok(())
    }

    pub fn commit_tx(&self) -> ChainResult<()> {
        let depth = self.tx_depth.get();
        if depth == 0 {
            return Ok(());
        }
        if depth == 1 {
            if let Err(e) = self.conn.execute("COMMIT", []) {
                // Do not leave `tx_depth` stuck at 1 (which would silently fold later dispatches
                // into one transaction): drop to 0 and try to roll back the open transaction.
                self.tx_depth.set(0);
                let _ = self.conn.execute("ROLLBACK", []);
                return Err(e.into());
            }
        } else if let Err(e) = self.conn.execute(&format!("RELEASE sp{}", depth - 1), []) {
            self.tx_depth.set(depth - 1);
            return Err(e.into());
        }
        self.tx_depth.set(depth - 1);
        Ok(())
    }

    pub fn rollback_tx(&self) -> ChainResult<()> {
        let depth = self.tx_depth.get();
        if depth == 0 {
            return Ok(());
        }
        if depth == 1 {
            self.conn.execute("ROLLBACK", [])?;
        } else {
            self.conn
                .execute(&format!("ROLLBACK TO sp{}", depth - 1), [])?;
            self.conn.execute(&format!("RELEASE sp{}", depth - 1), [])?;
        }
        self.tx_depth.set(depth - 1);
        Ok(())
    }

    /// The seed stored for the current run, when `init` recorded one.
    pub fn run_seed(&self) -> ChainResult<Option<String>> {
        self.row_text("SELECT value FROM chain_config WHERE key = 'seed'", [])
    }

    pub fn set_run_seed(&self, seed: &str) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO chain_config (key, value) VALUES ('seed', ?1)
             ON CONFLICT(key) DO UPDATE SET value = ?1",
            params![seed],
        )?;
        Ok(())
    }

    pub fn config_value(&self, key: &str) -> ChainResult<Option<String>> {
        self.row_text(
            "SELECT value FROM chain_config WHERE key = ?1",
            params![key],
        )
    }

    pub fn set_config_value(&self, key: &str, value: &str) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO chain_config (key, value) VALUES (?1, ?2)
             ON CONFLICT(key) DO UPDATE SET value = ?2",
            params![key, value],
        )?;
        Ok(())
    }

    // ---------------------------------------------------------------- settlement aliases (CLI convenience)

    /// The pallet has no numeric settlement ids; the CLI shows `settlement_ref` as a rowid in
    /// `settlement_aliases` so scripts can name settlements. This is a display convenience, not
    /// pallet storage.
    pub fn create_settlement_alias(&self, settlement_ref: &SettlementRef) -> ChainResult<i64> {
        self.conn.execute(
            "INSERT INTO settlement_aliases (settlement_ref) VALUES (?1)",
            params![settlement_ref.0.to_vec()],
        )?;
        Ok(self.conn.last_insert_rowid())
    }

    /// Alias id for a settlement ref, assigning one on first sight. Generation paths call
    /// this so `-S <id>` is usable before the settlement proof is applied; apply paths reuse
    /// the same id.
    pub fn ensure_settlement_alias(&self, settlement_ref: &SettlementRef) -> ChainResult<i64> {
        self.conn.execute(
            "INSERT INTO settlement_aliases (settlement_ref) VALUES (?1) ON CONFLICT(settlement_ref) DO NOTHING",
            params![settlement_ref.0.to_vec()],
        )?;
        self.conn
            .query_row(
                "SELECT id FROM settlement_aliases WHERE settlement_ref = ?1",
                params![settlement_ref.0.to_vec()],
                |row| row.get(0),
            )
            .map_err(ChainFailure::from)
    }

    pub fn resolve_settlement_alias(&self, id: i64) -> ChainResult<SettlementRef> {
        let blob: Vec<u8> = self
            .conn
            .query_row(
                "SELECT settlement_ref FROM settlement_aliases WHERE id = ?1",
                params![id],
                |row| row.get(0),
            )
            .optional()?
            .ok_or(ChainFailure::Error(ChainError::SettlementNotFound))?;
        let bytes: [u8; 32] = blob
            .try_into()
            .map_err(|_| ChainFailure::Internal("bad settlement ref".into()))?;
        Ok(SettlementRef(bytes))
    }

    pub fn settlement_alias(&self, settlement_ref: &SettlementRef) -> ChainResult<Option<i64>> {
        let id = self.lookup_i64(
            "SELECT id FROM settlement_aliases WHERE settlement_ref = ?1",
            &settlement_ref.0.to_vec(),
        )?;
        Ok(id)
    }

    // ---------------------------------------------------------------- chain state (frame_system / pallet_timestamp)

    pub fn block_number(&self) -> ChainResult<BlockNumber> {
        let v: i64 = self
            .conn
            .query_row(
                "SELECT block_number FROM chain_state WHERE id = 1",
                [],
                |row| row.get(0),
            )
            .optional()?
            .unwrap_or(1);
        Ok(u32_from_i64(v)?)
    }

    pub fn set_block_number(&self, block: BlockNumber) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO chain_state (id, block_number, moment) VALUES (1, ?1, 0)
             ON CONFLICT(id) DO UPDATE SET block_number = ?1",
            params![block as i64],
        )?;
        Ok(())
    }

    pub fn timestamp(&self) -> ChainResult<Moment> {
        let v: i64 = self
            .conn
            .query_row("SELECT moment FROM chain_state WHERE id = 1", [], |row| {
                row.get(0)
            })
            .optional()?
            .unwrap_or(0);
        Ok(from_i64(v)?)
    }

    pub fn set_timestamp(&self, moment: Moment) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO chain_state (id, block_number, moment) VALUES (1, 1, ?1)
             ON CONFLICT(id) DO UPDATE SET moment = ?1",
            params![to_i64(moment)?],
        )?;
        Ok(())
    }

    /// `frame_system` advance + `pallet_timestamp::set`. The CLI's `end-block` is the only thing that
    /// moves the clock, so time advances by `block_time` per block.
    pub fn advance_block(&self) -> ChainResult<(BlockNumber, Moment)> {
        let block = self.block_number()? + 1;
        let moment = self.timestamp()? + self.config.block_time;
        self.set_block_number(block)?;
        self.set_timestamp(moment)?;
        Ok((block, moment))
    }

    // ---------------------------------------------------------------- tree state

    pub fn tree_height(&self, tree: TreeKind) -> ChainResult<u8> {
        let v = self.row_i64(
            "SELECT height FROM tree_state WHERE tree = ?1",
            params![tree.name()],
        )?;
        u8_from_i64(v)
    }

    pub fn set_tree_height(&self, tree: TreeKind, height: u8) -> ChainResult<()> {
        self.conn.execute(
            "UPDATE tree_state SET height = ?1 WHERE tree = ?2",
            params![height as i64, tree.name()],
        )?;
        Ok(())
    }

    pub fn next_leaf_index(&self, tree: TreeKind) -> ChainResult<u64> {
        from_i64(self.row_i64(
            "SELECT next_leaf_index FROM tree_state WHERE tree = ?1",
            params![tree.name()],
        )?)
    }

    pub fn set_next_leaf_index(&self, tree: TreeKind, index: u64) -> ChainResult<()> {
        self.conn.execute(
            "UPDATE tree_state SET next_leaf_index = ?1 WHERE tree = ?2",
            params![to_i64(index)?, tree.name()],
        )?;
        Ok(())
    }

    pub fn last_committed_leaf_index(&self, tree: TreeKind) -> ChainResult<u64> {
        from_i64(self.row_i64(
            "SELECT last_committed_leaf_index FROM tree_state WHERE tree = ?1",
            params![tree.name()],
        )?)
    }

    pub fn set_last_committed_leaf_index(&self, tree: TreeKind, index: u64) -> ChainResult<()> {
        self.conn.execute(
            "UPDATE tree_state SET last_committed_leaf_index = ?1 WHERE tree = ?2",
            params![to_i64(index)?, tree.name()],
        )?;
        Ok(())
    }

    pub fn last_pruned_block(&self, tree: TreeKind) -> ChainResult<u32> {
        let v = self.row_i64(
            "SELECT last_pruned_block FROM tree_state WHERE tree = ?1",
            params![tree.name()],
        )?;
        u32_from_i64(v)
    }

    pub fn set_last_pruned_block(&self, tree: TreeKind, block: BlockNumber) -> ChainResult<()> {
        self.conn.execute(
            "UPDATE tree_state SET last_pruned_block = ?1 WHERE tree = ?2",
            params![block as i64, tree.name()],
        )?;
        Ok(())
    }

    pub fn last_update(&self, tree: TreeKind) -> ChainResult<Moment> {
        from_i64(self.row_i64(
            "SELECT last_update_moment FROM tree_state WHERE tree = ?1",
            params![tree.name()],
        )?)
    }

    pub fn set_last_update(&self, tree: TreeKind, moment: Moment) -> ChainResult<()> {
        self.conn.execute(
            "UPDATE tree_state SET last_update_moment = ?1 WHERE tree = ?2",
            params![to_i64(moment)?, tree.name()],
        )?;
        Ok(())
    }

    pub fn current_root(&self, tree: TreeKind) -> ChainResult<Option<Vec<u8>>> {
        self.conn
            .query_row(
                "SELECT current_root FROM tree_state WHERE tree = ?1",
                params![tree.name()],
                |row| row.get::<_, Option<Vec<u8>>>(0),
            )
            .optional()
            .map_err(ChainFailure::from)
            .map(|o| o.flatten())
    }

    pub fn set_current_root(&self, tree: TreeKind, root: &[u8]) -> ChainResult<()> {
        self.conn.execute(
            "UPDATE tree_state SET current_root = ?1 WHERE tree = ?2",
            params![root, tree.name()],
        )?;
        Ok(())
    }

    /// `store_*_curve_tree_root`: one row per (tree, block), replaced within the same block.
    pub fn store_root(
        &self,
        tree: TreeKind,
        block: BlockNumber,
        height: u8,
        moment: Moment,
        root: &[u8],
    ) -> ChainResult<BlockNumber> {
        self.conn.execute(
            "INSERT INTO tree_roots (tree, block_number, height, moment, root_data) VALUES (?1, ?2, ?3, ?4, ?5)
             ON CONFLICT(tree, block_number) DO UPDATE SET height = ?3, moment = ?4, root_data = ?5",
            params![tree.name(), block as i64, height as i64, to_i64(moment)?, root],
        )?;
        self.set_last_update(tree, moment)?;
        self.set_current_root(tree, root)?;
        Ok(block)
    }

    /// `get_*_curve_tree_root`: the root for `block`, only if it is still within the max age.
    pub fn get_block_root(
        &self,
        tree: TreeKind,
        block: BlockNumber,
    ) -> ChainResult<Option<Vec<u8>>> {
        let row: Option<(Vec<u8>, i64)> = self
            .conn
            .query_row(
                "SELECT root_data, moment FROM tree_roots WHERE tree = ?1 AND block_number = ?2",
                params![tree.name(), block as i64],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?;
        let Some((root, moment)) = row else {
            return Ok(None);
        };
        let now = self.timestamp()?;
        let age = now.saturating_sub(from_i64(moment)?);
        if age > self.config.max_age(tree) {
            return Ok(None);
        }
        Ok(Some(root))
    }

    /// `root_pruning`: prune expired roots for one tree, at most `MAX_ROOT_PRUNING_BLOCKS` blocks.
    pub fn prune_roots(&self, tree: TreeKind) -> ChainResult<u32> {
        let stop_at = self
            .block_number()?
            .saturating_sub(self.config.recent_blocks_to_keep);
        let mut last_pruned = self.last_pruned_block(tree)?;
        let mut pruned = 0;
        for _ in 0..self.config.max_root_pruning_blocks {
            let block = last_pruned.saturating_add(1);
            if block >= stop_at {
                break;
            }
            if self.get_block_root(tree, block)?.is_some() {
                // `get_block_root` applies the max-age check, so a hit means the root is still
                // valid and pruning stops here.
                break;
            }
            self.conn.execute(
                "DELETE FROM tree_roots WHERE tree = ?1 AND block_number = ?2",
                params![tree.name(), block as i64],
            )?;
            last_pruned = block;
            pruned += 1;
        }
        self.set_last_pruned_block(tree, last_pruned)?;
        Ok(pruned)
    }

    pub fn root_blocks(&self, tree: TreeKind) -> ChainResult<Vec<BlockNumber>> {
        let mut stmt = self
            .conn
            .prepare("SELECT block_number FROM tree_roots WHERE tree = ?1 ORDER BY block_number")?;
        let rows = stmt.query_map(params![tree.name()], |row| row.get::<_, i64>(0))?;
        let mut out = Vec::new();
        for row in rows {
            out.push(u32_from_i64(row?)?);
        }
        Ok(out)
    }

    /// The block of the most recently stored root for `tree` — the root a prover (client) sees.
    pub fn last_root_block(&self, tree: TreeKind) -> ChainResult<Option<BlockNumber>> {
        // `MAX` over an empty table yields one NULL row; `OptionalExtension` does not turn that
        // into `None`, so unwrap the nullable column explicitly and then the row.
        let row: Option<Option<i64>> = self
            .conn
            .query_row(
                "SELECT MAX(block_number) FROM tree_roots WHERE tree = ?1",
                params![tree.name()],
                |row| row.get(0),
            )
            .optional()?;
        match row.flatten() {
            Some(block) => Ok(Some(u32_from_i64(block)?)),
            None => Ok(None),
        }
    }

    // ---------------------------------------------------------------- tree leaves / inner nodes

    pub fn get_leaf(&self, tree: TreeKind, leaf_index: u64) -> ChainResult<Option<Vec<u8>>> {
        self.conn
            .query_row(
                "SELECT leaf_data FROM tree_leaves WHERE tree = ?1 AND leaf_index = ?2",
                params![tree.name(), to_i64(leaf_index)?],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .optional()
            .map_err(ChainFailure::from)
    }

    /// `set_leaf` for a tree that allows updates (the asset tree), and the append-only insert path
    /// used by the account and fee trees.
    pub fn set_leaf(
        &self,
        tree: TreeKind,
        leaf_index: u64,
        leaf: &[u8],
        append_only: bool,
    ) -> ChainResult<Option<Vec<u8>>> {
        let old = self.get_leaf(tree, leaf_index)?;
        if append_only && old.is_some() {
            return Err(ChainFailure::Internal(
                "cannot update a leaf in an append-only tree".into(),
            ));
        }
        self.conn.execute(
            "INSERT OR REPLACE INTO tree_leaves (tree, leaf_index, leaf_data) VALUES (?1, ?2, ?3)",
            params![tree.name(), to_i64(leaf_index)?, leaf],
        )?;
        Ok(old)
    }

    pub fn leaf_count(&self, tree: TreeKind) -> ChainResult<u64> {
        from_i64(self.row_i64(
            "SELECT COUNT(*) FROM tree_leaves WHERE tree = ?1",
            params![tree.name()],
        )?)
    }

    pub fn find_leaf_index(&self, tree: TreeKind, leaf: &[u8]) -> ChainResult<Option<u64>> {
        let row: Option<i64> = self
            .conn
            .query_row(
                "SELECT leaf_index FROM tree_leaves WHERE tree = ?1 AND leaf_data = ?2",
                params![tree.name(), leaf],
                |row| row.get(0),
            )
            .optional()?;
        row.map(from_i64).transpose()
    }

    pub fn get_inner_node(&self, tree: TreeKind, location: &[u8]) -> ChainResult<Option<Vec<u8>>> {
        self.conn
            .query_row(
                "SELECT node_data FROM tree_inner_nodes WHERE tree = ?1 AND location = ?2",
                params![tree.name(), location],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .optional()
            .map_err(ChainFailure::from)
    }

    pub fn set_inner_node(&self, tree: TreeKind, location: &[u8], node: &[u8]) -> ChainResult<()> {
        self.conn.execute(
            "INSERT OR REPLACE INTO tree_inner_nodes (tree, location, node_data) VALUES (?1, ?2, ?3)",
            params![tree.name(), location, node],
        )?;
        Ok(())
    }

    // ---------------------------------------------------------------- nullifiers

    pub fn nullifier_used(&self, tree: TreeKind, nullifier: &[u8]) -> ChainResult<bool> {
        let count = self.row_i64(
            "SELECT COUNT(*) FROM tree_nullifiers WHERE tree = ?1 AND nullifier = ?2",
            params![tree.name(), nullifier],
        )?;
        Ok(count > 0)
    }

    /// `ensure_*_state_nullifier_unique` + burn.
    pub fn burn_nullifier(&self, tree: TreeKind, nullifier: &[u8]) -> ChainResult<()> {
        if self.nullifier_used(tree, nullifier)? {
            return Err(ChainFailure::Error(ChainError::NullifierAlreadyUsed));
        }
        self.conn.execute(
            "INSERT INTO tree_nullifiers (tree, nullifier) VALUES (?1, ?2)",
            params![tree.name(), nullifier],
        )?;
        Ok(())
    }

    // ---------------------------------------------------------------- identities and accounts

    pub fn create_identity(&self, name: &str) -> ChainResult<i64> {
        self.conn.execute(
            "INSERT INTO identities (name, did) VALUES (?1, ?2)",
            params![name, signer_to_did(name)?.to_vec()],
        )?;
        Ok(self.conn.last_insert_rowid())
    }

    pub fn identity_id(&self, name: &str) -> ChainResult<i64> {
        self.conn
            .query_row(
                "SELECT id FROM identities WHERE name = ?1",
                params![name],
                |row| row.get(0),
            )
            .optional()
            .map_err(ChainFailure::from)?
            .ok_or_else(|| ChainFailure::Error(ChainError::BadOrigin))
    }

    pub fn did_for_identity(&self, id: i64) -> ChainResult<Did> {
        let bytes: Vec<u8> = self.conn.query_row(
            "SELECT did FROM identities WHERE id = ?1",
            params![id],
            |row| row.get(0),
        )?;
        let did: [u8; 32] = bytes
            .try_into()
            .map_err(|_| ChainFailure::Internal("bad did".into()))?;
        Ok(did)
    }

    // ---------------------------------------------------------------- accounts, assets, legs

    /// `AccountDid`.
    pub fn account_did(&self, account: &AccountPublicKey) -> ChainResult<Option<i64>> {
        self.lookup_i64(
            "SELECT identity_id FROM account_did WHERE account_key = ?1",
            &account.encode(),
        )
    }

    /// `FeeAccountDid`.
    pub fn fee_account_did(&self, account: &AccountPublicKey) -> ChainResult<Option<i64>> {
        self.lookup_i64(
            "SELECT identity_id FROM fee_account_did WHERE account_key = ?1",
            &account.encode(),
        )
    }

    /// `EncryptionKeyDid`.
    pub fn encryption_key_did(&self, key: &EncryptionPublicKey) -> ChainResult<Option<i64>> {
        self.lookup_i64(
            "SELECT identity_id FROM encryption_key_did WHERE enc_key = ?1",
            &key.encode(),
        )
    }

    pub fn insert_account_did(
        &self,
        account: &AccountPublicKey,
        identity_id: i64,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO account_did (account_key, identity_id) VALUES (?1, ?2)",
            params![account.encode(), identity_id],
        )?;
        Ok(())
    }

    pub fn insert_fee_account_did(
        &self,
        account: &AccountPublicKey,
        identity_id: i64,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO fee_account_did (account_key, identity_id) VALUES (?1, ?2)",
            params![account.encode(), identity_id],
        )?;
        Ok(())
    }

    /// Registered fee accounts: `(hex account key, owner identity name)`.
    pub fn list_fee_accounts(&self) -> ChainResult<Vec<(String, String)>> {
        let mut stmt = self
            .conn
            .prepare("SELECT account_key, identities.name FROM fee_account_did JOIN identities ON identities.id = identity_id ORDER BY fee_account_did.rowid")?;
        let rows = stmt.query_map([], |row| {
            let key: Vec<u8> = row.get(0)?;
            let name: String = row.get(1)?;
            Ok((hex::encode(key), name))
        })?;
        rows.collect::<Result<Vec<_>, _>>()
            .map_err(ChainFailure::from)
    }

    pub fn insert_encryption_key_did(
        &self,
        key: &EncryptionPublicKey,
        identity_id: i64,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO encryption_key_did (enc_key, identity_id) VALUES (?1, ?2)",
            params![key.encode(), identity_id],
        )?;
        Ok(())
    }

    /// `DidAccounts`.
    pub fn insert_did_account(
        &self,
        identity_id: i64,
        account: &AccountPublicKey,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO did_accounts (identity_id, account_key) VALUES (?1, ?2)",
            params![identity_id, account.encode()],
        )?;
        Ok(())
    }

    /// `AccountEncryptionKey`.
    pub fn account_encryption_key(
        &self,
        account: &AccountPublicKey,
    ) -> ChainResult<Option<EncryptionPublicKey>> {
        let blob = self
            .conn
            .query_row(
                "SELECT enc_key FROM account_encryption_key WHERE account_key = ?1",
                params![account.encode()],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .optional()?;
        blob.map(|b| EncryptionPublicKey::decode(&mut b.as_slice()))
            .transpose()
            .map_err(ChainFailure::from)
    }

    pub fn insert_account_encryption_key(
        &self,
        account: &AccountPublicKey,
        key: &EncryptionPublicKey,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO account_encryption_key (account_key, enc_key) VALUES (?1, ?2)",
            params![account.encode(), key.encode()],
        )?;
        Ok(())
    }

    /// `EncryptionKeyAccount`.
    pub fn insert_encryption_key_account(
        &self,
        key: &EncryptionPublicKey,
        account: &AccountPublicKey,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO encryption_key_account (enc_key, account_key) VALUES (?1, ?2)",
            params![key.encode(), account.encode()],
        )?;
        Ok(())
    }

    /// `AccountAssetRegistrations`.
    pub fn account_asset_registered(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
    ) -> ChainResult<bool> {
        let found = self
            .conn
            .query_row(
                "SELECT 1 FROM account_asset_registrations WHERE account_key = ?1 AND asset_id = ?2",
                params![account.encode(), asset_id as i64],
                |row| row.get::<_, i64>(0),
            )
            .optional()?;
        Ok(found.is_some())
    }

    pub fn insert_account_asset_registration(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO account_asset_registrations (account_key, asset_id) VALUES (?1, ?2)",
            params![account.encode(), asset_id as i64],
        )?;
        Ok(())
    }

    /// `Keys` — the asset's auditor and mediator keys.
    pub fn asset_keys(&self, asset_id: AssetId) -> ChainResult<Option<AssetKeys>> {
        let row = self
            .conn
            .query_row(
                "SELECT enc_keys, mediators FROM asset_keys WHERE asset_id = ?1",
                params![asset_id as i64],
                |row| Ok((row.get::<_, Vec<u8>>(0)?, row.get::<_, Vec<u8>>(1)?)),
            )
            .optional()?;
        match row {
            None => Ok(None),
            Some((enc_keys, mediators)) => Ok(Some(AssetKeys {
                enc_keys: Decode::decode(&mut enc_keys.as_slice())?,
                mediators: Decode::decode(&mut mediators.as_slice())?,
            })),
        }
    }

    /// `AssetFrozen`.
    pub fn asset_frozen(&self, asset_id: AssetId) -> ChainResult<Option<String>> {
        self.row_text(
            "SELECT freeze_origin FROM asset_frozen WHERE asset_id = ?1",
            params![asset_id as i64],
        )
    }

    /// `NextAssetId` — the next free asset id. The pallet keeps a counter; the CLI derives it from
    /// the highest allocated id, which matches the counter as long as ids stay contiguous from 0.
    pub fn next_asset_id(&self) -> ChainResult<AssetId> {
        self.conn
            .query_row(
                "SELECT COALESCE(MAX(asset_id), -1) + 1 FROM assets",
                [],
                |row| row.get::<_, i64>(0),
            )
            .map(|v| u32::try_from(v).ok())
            .optional()?
            .flatten()
            .ok_or(ChainFailure::Error(ChainError::AssetIdOverflow))
    }

    /// `Details` — asset metadata plus the running total supply.
    pub fn asset_details(&self, asset_id: AssetId) -> ChainResult<Option<AssetDetails>> {
        let row = self
            .conn
            .query_row(
                "SELECT name, symbol, decimals, issuer_identity_id, total_supply FROM assets WHERE asset_id = ?1",
                params![asset_id as i64],
                |row| {
                    Ok((
                        row.get::<_, String>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, i64>(2)?,
                        row.get::<_, i64>(3)?,
                        row.get::<_, i64>(4)?,
                    ))
                },
            )
            .optional()?;
        match row {
            None => Ok(None),
            Some((name, symbol, decimals, issuer_identity_id, total_supply)) => {
                Ok(Some(AssetDetails {
                    name,
                    symbol,
                    decimals: u8_from_i64(decimals)?,
                    issuer_identity_id,
                    total_supply: from_i64(total_supply)?,
                }))
            }
        }
    }

    /// `SettlementLegs`.
    pub fn settlement_leg(
        &self,
        settlement_ref: &SettlementRef,
        leg_id: LegId,
    ) -> ChainResult<Option<LegEncrypted>> {
        let blob = self
            .conn
            .query_row(
                "SELECT leg_enc FROM settlement_legs WHERE settlement_ref = ?1 AND leg_id = ?2",
                params![settlement_ref.0.to_vec(), leg_id as i64],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .optional()?;
        blob.map(|b| <LegEncrypted as Decode>::decode(&mut b.as_slice()))
            .transpose()
            .map_err(ChainFailure::from)
    }

    // ---------------------------------------------------------------- prover state (no pallet equivalent)

    pub fn prover_account_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
    ) -> ChainResult<Option<AccountAssetState>> {
        let blob = self
            .conn
            .query_row(
                "SELECT state_data FROM prover_account_states WHERE account_key = ?1 AND asset_id = ?2",
                params![account.encode(), asset_id as i64],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .optional()?;
        blob.map(|b| AccountAssetState::decode(&mut b.as_slice()))
            .transpose()
            .map_err(ChainFailure::from)
    }

    pub fn set_prover_account_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
        state: &AccountAssetState,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO prover_account_states (account_key, asset_id, state_data) VALUES (?1, ?2, ?3)
             ON CONFLICT(account_key, asset_id) DO UPDATE SET state_data = ?3",
            params![account.encode(), asset_id as i64, state.encode()],
        )?;
        Ok(())
    }

    /// All prover states for one account, keyed by asset id (used to promote pending states
    /// after an accepted settlement transaction).
    pub fn pending_prover_states(
        &self,
        account: &AccountPublicKey,
    ) -> ChainResult<Vec<(AssetId, AccountAssetState)>> {
        let mut stmt = self.conn.prepare(
            "SELECT asset_id, state_data FROM prover_account_states WHERE account_key = ?1",
        )?;
        let rows = stmt
            .query_map(params![account.encode()], |row| {
                Ok((row.get::<_, i64>(0)?, row.get::<_, Vec<u8>>(1)?))
            })?
            .collect::<Result<Vec<_>, _>>()?;
        let mut out = Vec::new();
        for (asset_id, blob) in rows {
            let asset_id = u32::try_from(asset_id)
                .map_err(|_| ChainFailure::Internal("bad asset id".into()))?;
            let state = AccountAssetState::decode(&mut blob.as_slice())?;
            out.push((asset_id, state));
        }
        Ok(out)
    }

    pub fn prover_fee_account_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
    ) -> ChainResult<Option<FeeAccountAssetState>> {
        let blob = self
            .conn
            .query_row(
                "SELECT state_data FROM prover_fee_account_states WHERE account_key = ?1 AND asset_id = ?2",
                params![account.encode(), asset_id as i64],
                |row| row.get::<_, Option<Vec<u8>>>(0),
            )
            .optional()?
            .flatten();
        blob.map(|b| FeeAccountAssetState::decode(&mut b.as_slice()))
            .transpose()
            .map_err(ChainFailure::from)
    }

    /// Host-side staging of a freshly generated fee state: `state_data` (the committed state)
    /// is only promoted from `pending_state_data` once the chain accepts the transaction, so a
    /// failed dispatch cannot clobber the prover state used by later top-ups.
    pub fn set_pending_fee_account_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
        state: &FeeAccountAssetState,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO prover_fee_account_states (account_key, asset_id, pending_state_data) VALUES (?1, ?2, ?3)
             ON CONFLICT(account_key, asset_id) DO UPDATE SET pending_state_data = ?3",
            params![account.encode(), asset_id as i64, state.encode()],
        )?;
        Ok(())
    }

    /// Take the staged fee state (clearing the pending slot); used by the driver's
    /// post-dispatch promotion, which commits the pending state first.
    pub fn take_pending_fee_account_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
    ) -> ChainResult<Option<FeeAccountAssetState>> {
        let blob = self
            .conn
            .query_row(
                "SELECT pending_state_data FROM prover_fee_account_states WHERE account_key = ?1 AND asset_id = ?2",
                params![account.encode(), asset_id as i64],
                |row| row.get::<_, Option<Vec<u8>>>(0),
            )
            .optional()?
            .flatten();
        self.conn.execute(
            "UPDATE prover_fee_account_states SET pending_state_data = NULL WHERE account_key = ?1 AND asset_id = ?2",
            params![account.encode(), asset_id as i64],
        )?;
        blob.map(|b| FeeAccountAssetState::decode(&mut b.as_slice()))
            .transpose()
            .map_err(ChainFailure::from)
    }

    /// Commit the staged fee state as the current prover state.
    pub fn set_current_fee_account_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
        state: &FeeAccountAssetState,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO prover_fee_account_states (account_key, asset_id, state_data) VALUES (?1, ?2, ?3)
             ON CONFLICT(account_key, asset_id) DO UPDATE SET state_data = ?3",
            params![account.encode(), asset_id as i64, state.encode()],
        )?;
        Ok(())
    }

    fn lookup_i64(&self, sql: &str, key: &[u8]) -> ChainResult<Option<i64>> {
        self.conn
            .query_row(sql, params![key], |row| row.get(0))
            .optional()
            .map_err(ChainFailure::from)
    }

    /// Host keystore: a generated encryption keypair (secret stays CLI-local, never chain state).
    pub fn insert_host_enc_key(
        &self,
        owner: &str,
        pair: &polymesh_dart::EncryptionKeyPair,
    ) -> ChainResult<i64> {
        self.conn.execute(
            "INSERT INTO host_enc_keys (owner, enc_key, secret) VALUES (?1, ?2, ?3)",
            params![owner, pair.public.encode(), pair.secret.encode()],
        )?;
        Ok(self.conn.last_insert_rowid())
    }

    pub fn host_enc_key(&self, id: i64) -> ChainResult<polymesh_dart::EncryptionKeyPair> {
        let blobs: (Vec<u8>, Vec<u8>) = self
            .conn
            .query_row(
                "SELECT enc_key, secret FROM host_enc_keys WHERE id = ?1",
                params![id],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?
            .ok_or_else(|| {
                ChainFailure::Internal(format!(
                    "no host encryption key with id {id} (run register-encryption-keys first)"
                ))
            })?;
        use codec::Decode as _;
        Ok(polymesh_dart::EncryptionKeyPair {
            public: polymesh_dart::EncryptionPublicKey::decode(&mut blobs.0.as_slice())
                .map_err(ChainFailure::from)?,
            secret: polymesh_dart::EncryptionSecretKey::decode(&mut blobs.1.as_slice())
                .map_err(ChainFailure::from)?,
        })
    }

    /// Host keystore id of a given public key, if present.
    pub fn host_enc_key_id(
        &self,
        key: &polymesh_dart::EncryptionPublicKey,
    ) -> ChainResult<Option<i64>> {
        self.conn
            .query_row(
                "SELECT id FROM host_enc_keys WHERE enc_key = ?1",
                params![key.encode()],
                |row| row.get(0),
            )
            .optional()
            .map_err(ChainFailure::from)
    }

    /// All host keystore key ids owned by a signer (generation order).
    pub fn host_enc_key_ids(&self, owner: &str) -> ChainResult<Vec<i64>> {
        let mut stmt = self
            .conn
            .prepare("SELECT id FROM host_enc_keys WHERE owner = ?1 ORDER BY id")?;
        let rows = stmt.query_map(params![owner], |row| row.get(0))?;
        rows.collect::<Result<Vec<_>, _>>()
            .map_err(ChainFailure::from)
    }

    /// Map a generated proof's nullifier to the prover state it advances (host-side
    /// bookkeeping so `submit_batched_proofs` can promote exactly the states the batch consumed).
    pub fn index_prover_state(
        &self,
        nullifier: &[u8],
        account: &AccountPublicKey,
        asset_id: AssetId,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT OR REPLACE INTO proof_state_index (nullifier, account_key, asset_id) VALUES (?1, ?2, ?3)",
            params![nullifier, account.encode(), asset_id as i64],
        )?;
        Ok(())
    }

    pub fn lookup_prover_state(
        &self,
        nullifier: &[u8],
    ) -> ChainResult<Option<(AccountPublicKey, AssetId)>> {
        let row: Option<(Vec<u8>, i64)> = self
            .conn
            .query_row(
                "SELECT account_key, asset_id FROM proof_state_index WHERE nullifier = ?1",
                params![nullifier],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?;
        let Some((key, asset)) = row else {
            return Ok(None);
        };
        let account = AccountPublicKey::decode(&mut key.as_slice()).map_err(ChainFailure::from)?;
        Ok(Some((account, asset as AssetId)))
    }

    pub fn create_account(
        &self,
        identity_id: i64,
        name: &str,
        key_seed: &str,
        public_keys: &AccountPublicKeys,
    ) -> ChainResult<i64> {
        self.conn.execute(
            "INSERT INTO accounts (identity_id, name, key_seed, account_key, enc_key) VALUES (?1, ?2, ?3, ?4, ?5)",
            params![
                identity_id,
                name,
                key_seed,
                public_keys.acct.encode(),
                public_keys.enc.encode()
            ],
        )?;
        Ok(self.conn.last_insert_rowid())
    }

    pub fn account(
        &self,
        identity_name: &str,
        account_name: &str,
    ) -> ChainResult<Option<AccountRow>> {
        let row = self
            .conn
            .query_row(
                "SELECT a.id, a.identity_id, a.name, a.key_seed, a.account_key, a.enc_key
                 FROM accounts a JOIN identities i ON a.identity_id = i.id
                 WHERE i.name = ?1 AND a.name = ?2",
                params![identity_name, account_name],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?,
                        row.get::<_, Vec<u8>>(4)?,
                        row.get::<_, Vec<u8>>(5)?,
                    ))
                },
            )
            .optional()?;
        row.map(to_account_row).transpose()
    }

    pub fn account_by_key(&self, account: &AccountPublicKey) -> ChainResult<Option<AccountRow>> {
        let row = self
            .conn
            .query_row(
                "SELECT id, identity_id, name, key_seed, account_key, enc_key FROM accounts WHERE account_key = ?1",
                params![account.encode()],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?,
                        row.get::<_, Vec<u8>>(4)?,
                        row.get::<_, Vec<u8>>(5)?,
                    ))
                },
            )
            .optional()?;
        row.map(to_account_row).transpose()
    }

    pub fn account_by_rowid(&self, id: i64) -> ChainResult<Option<AccountRow>> {
        let row = self
            .conn
            .query_row(
                "SELECT id, identity_id, name, key_seed, account_key, enc_key FROM accounts WHERE id = ?1",
                params![id],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, i64>(1)?,
                        row.get::<_, String>(2)?,
                        row.get::<_, String>(3)?,
                        row.get::<_, Vec<u8>>(4)?,
                        row.get::<_, Vec<u8>>(5)?,
                    ))
                },
            )
            .optional()?;
        row.map(to_account_row).transpose()
    }

    // ---------------------------------------------------------------- list helpers (CLI queries)

    pub fn list_identities(&self) -> ChainResult<Vec<(i64, String)>> {
        let mut stmt = self
            .conn
            .prepare("SELECT id, name FROM identities ORDER BY name")?;
        let rows = stmt.query_map([], |row| Ok((row.get(0)?, row.get(1)?)))?;
        rows.collect::<Result<Vec<_>, _>>()
            .map_err(ChainFailure::from)
    }

    pub fn list_accounts(
        &self,
        signer_name: Option<&str>,
    ) -> ChainResult<Vec<(String, AccountRow)>> {
        let query = if signer_name.is_some() {
            "SELECT a.id, a.identity_id, a.name, a.key_seed, a.account_key, a.enc_key, i.name
             FROM accounts a JOIN identities i ON a.identity_id = i.id
             WHERE i.name = ?1 ORDER BY i.name, a.name"
        } else {
            "SELECT a.id, a.identity_id, a.name, a.key_seed, a.account_key, a.enc_key, i.name
             FROM accounts a JOIN identities i ON a.identity_id = i.id
             ORDER BY i.name, a.name"
        };
        let mut stmt = self.conn.prepare(query)?;
        let map = |row: &rusqlite::Row| -> rusqlite::Result<(String, (i64, i64, String, String, Vec<u8>, Vec<u8>))> {
            Ok((
                row.get::<_, String>(6)?,
                (
                    row.get::<_, i64>(0)?,
                    row.get::<_, i64>(1)?,
                    row.get::<_, String>(2)?,
                    row.get::<_, String>(3)?,
                    row.get::<_, Vec<u8>>(4)?,
                    row.get::<_, Vec<u8>>(5)?,
                ),
            ))
        };
        let rows: Vec<(String, (i64, i64, String, String, Vec<u8>, Vec<u8>))> =
            if let Some(signer) = signer_name {
                stmt.query_map(params![signer], map)?
                    .collect::<Result<Vec<_>, _>>()?
            } else {
                stmt.query_map([], map)?.collect::<Result<Vec<_>, _>>()?
            };
        rows.into_iter()
            .map(|(signer, row)| Ok((signer, to_account_row(row)?)))
            .collect()
    }

    /// All stored root blocks for a tree (ascending).
    pub fn list_root_blocks(&self, tree: TreeKind) -> ChainResult<Vec<BlockNumber>> {
        let mut stmt = self
            .conn
            .prepare("SELECT block_number FROM tree_roots WHERE tree = ?1 ORDER BY block_number")?;
        let rows = stmt.query_map(params![tree.name()], |row| {
            let b: i64 = row.get(0)?;
            Ok(b as BlockNumber)
        })?;
        rows.collect::<Result<Vec<_>, _>>()
            .map_err(ChainFailure::from)
    }

    pub fn list_settlements(&self) -> ChainResult<Vec<(i64, String)>> {
        let mut stmt = self.conn.prepare(
            "SELECT a.id, s.status FROM settlement_aliases a JOIN settlement_state s ON s.settlement_ref = a.settlement_ref ORDER BY a.id",
        )?;
        let rows = stmt.query_map([], |row| Ok((row.get(0)?, row.get(1)?)))?;
        rows.collect::<Result<Vec<_>, _>>()
            .map_err(ChainFailure::from)
    }

    pub fn claim_count(&self) -> ChainResult<i64> {
        self.row_i64("SELECT COUNT(*) FROM claims", [])
    }

    pub fn list_assets(&self) -> ChainResult<Vec<(AssetId, AssetDetails)>> {
        let mut stmt = self.conn.prepare(
            "SELECT asset_id, name, symbol, decimals, issuer_identity_id, total_supply FROM assets ORDER BY asset_id",
        )?;
        let rows = stmt.query_map([], |row| {
            Ok((
                u32::try_from(row.get::<_, i64>(0)?).map_err(|_| {
                    rusqlite::Error::InvalidColumnType(
                        0,
                        "asset_id".into(),
                        rusqlite::types::Type::Integer,
                    )
                })?,
                row.get::<_, String>(1)?,
                row.get::<_, String>(2)?,
                row.get::<_, i64>(3)?,
                row.get::<_, i64>(4)?,
                row.get::<_, i64>(5)?,
            ))
        })?;
        let mut out = Vec::new();
        for row in rows {
            let (asset_id, name, symbol, decimals, issuer, total_supply) = row?;
            out.push((
                asset_id,
                AssetDetails {
                    name,
                    symbol,
                    decimals: u8::try_from(decimals).unwrap_or(0),
                    issuer_identity_id: issuer,
                    total_supply: u64::try_from(total_supply).unwrap_or(0),
                },
            ));
        }
        Ok(out)
    }

    /// Settlement status by CLI alias.
    pub fn settlement_status(&self, settlement_id: i64) -> ChainResult<String> {
        let settlement_ref = self.resolve_settlement_alias(settlement_id)?;
        self.row_text(
            "SELECT status FROM settlement_state WHERE settlement_ref = ?1",
            params![settlement_ref.0.to_vec()],
        )?
        .ok_or_else(|| ChainFailure::Error(ChainError::SettlementNotFound))
    }

    /// Per-party leg statuses for a settlement (reviewer view; GAPS.md §5).
    pub fn show_legs(&self, settlement_id: i64) -> ChainResult<Vec<(LegId, String, String)>> {
        let settlement_ref = self.resolve_settlement_alias(settlement_id)?;
        self.leg_statuses(&settlement_ref)
    }

    // ---------------------------------------------------------------- settlement helpers

    /// `SettlementLegs::insert`.
    pub fn insert_settlement_leg(
        &self,
        settlement_ref: &SettlementRef,
        leg_id: LegId,
        leg_enc: &LegEncrypted,
    ) -> ChainResult<()> {
        // `INSERT OR REPLACE`: the generation path pre-seeds the leg rows (so parties can
        // build proofs before apply); the apply path rewrites the identical rows.
        self.conn.execute(
            "INSERT OR REPLACE INTO settlement_legs (settlement_ref, leg_id, leg_enc) VALUES (?1, ?2, ?3)",
            params![settlement_ref.0.to_vec(), leg_id as i64, leg_enc.encode()],
        )?;
        Ok(())
    }

    /// `LegMediators::insert` — the creation-time mediator snapshot for a revealed-asset leg.
    pub fn insert_leg_mediators(
        &self,
        settlement_ref: &SettlementRef,
        leg_id: LegId,
        mediators: &[AccountPublicKey],
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT OR REPLACE INTO leg_mediators (settlement_ref, leg_id, mediators) VALUES (?1, ?2, ?3)",
            params![
                settlement_ref.0.to_vec(),
                leg_id as i64,
                mediators.to_vec().encode()
            ],
        )?;
        Ok(())
    }

    /// `LegMediators::get`.
    pub fn leg_mediators(
        &self,
        settlement_ref: &SettlementRef,
        leg_id: LegId,
    ) -> ChainResult<Option<Vec<AccountPublicKey>>> {
        let blob = self
            .conn
            .query_row(
                "SELECT mediators FROM leg_mediators WHERE settlement_ref = ?1 AND leg_id = ?2",
                params![settlement_ref.0.to_vec(), leg_id as i64],
                |row| row.get::<_, Vec<u8>>(0),
            )
            .optional()?;
        blob.map(|b| Decode::decode(&mut b.as_slice()))
            .transpose()
            .map_err(ChainFailure::from)
    }

    /// `LegAffirmationStatus::insert` for one party.
    pub fn insert_leg_status(
        &self,
        settlement_ref: &SettlementRef,
        leg_id: LegId,
        party: &str,
        status: &str,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO leg_affirmation_status (settlement_ref, leg_id, party, status) VALUES (?1, ?2, ?3, ?4)",
            params![settlement_ref.0.to_vec(), leg_id as i64, party, status],
        )?;
        Ok(())
    }

    /// `SettlementPendingAffirmations::insert`.
    pub fn set_pending_affirmations(
        &self,
        settlement_ref: &SettlementRef,
        count: u32,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO settlement_pending_affirmations (settlement_ref, pending) VALUES (?1, ?2)
             ON CONFLICT(settlement_ref) DO UPDATE SET pending = ?2",
            params![settlement_ref.0.to_vec(), count as i64],
        )?;
        Ok(())
    }

    /// `SettlementPendingFinalizations::insert(0)` at creation.
    pub fn init_pending_finalizations(&self, settlement_ref: &SettlementRef) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO settlement_pending_finalizations (settlement_ref, pending) VALUES (?1, 0)",
            params![settlement_ref.0.to_vec()],
        )?;
        Ok(())
    }

    /// `SettlementMemo::insert`.
    pub fn set_memo(&self, settlement_ref: &SettlementRef, memo: &[u8]) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO settlement_memo (settlement_ref, memo) VALUES (?1, ?2)
             ON CONFLICT(settlement_ref) DO UPDATE SET memo = ?2",
            params![settlement_ref.0.to_vec(), memo],
        )?;
        Ok(())
    }

    /// `SettlementLegCount::insert`.
    pub fn set_leg_count(&self, settlement_ref: &SettlementRef, count: u32) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO settlement_leg_count (settlement_ref, leg_count) VALUES (?1, ?2)
             ON CONFLICT(settlement_ref) DO UPDATE SET leg_count = ?2",
            params![settlement_ref.0.to_vec(), count as i64],
        )?;
        Ok(())
    }

    pub fn leg_statuses(
        &self,
        settlement_ref: &SettlementRef,
    ) -> ChainResult<Vec<(LegId, String, String)>> {
        let mut stmt = self.conn.prepare(
            "SELECT leg_id, party, status FROM leg_affirmation_status WHERE settlement_ref = ?1 ORDER BY leg_id, party",
        )?;
        let rows = stmt.query_map(params![settlement_ref.0.to_vec()], |row| {
            Ok((row.get::<_, i64>(0)? as LegId, row.get(1)?, row.get(2)?))
        })?;
        rows.collect::<Result<Vec<_>, _>>()
            .map_err(ChainFailure::from)
    }

    // ---------------------------------------------------------------- assets

    /// `Details::insert` plus the metadata storage items the CLI folds into one row.
    #[allow(clippy::too_many_arguments)]
    pub fn insert_asset(
        &self,
        asset_id: AssetId,
        name: &str,
        symbol: &str,
        decimals: u8,
        data: &[u8],
        issuer_identity_id: i64,
    ) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO assets (asset_id, name, symbol, decimals, data, issuer_identity_id, total_supply) VALUES (?1, ?2, ?3, ?4, ?5, ?6, 0)",
            params![asset_id as i64, name, symbol, decimals as i64, data, issuer_identity_id],
        )?;
        Ok(())
    }

    /// `Details::insert` — the running total supply.
    pub fn set_asset_total_supply(&self, asset_id: AssetId, supply: u64) -> ChainResult<()> {
        self.conn.execute(
            "UPDATE assets SET total_supply = ?2 WHERE asset_id = ?1",
            params![asset_id as i64, to_i64(supply)?],
        )?;
        Ok(())
    }

    /// `Keys::insert`.
    pub fn insert_asset_keys(&self, asset_id: AssetId, keys: &AssetKeys) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO asset_keys (asset_id, enc_keys, mediators) VALUES (?1, ?2, ?3)
             ON CONFLICT(asset_id) DO UPDATE SET enc_keys = ?2, mediators = ?3",
            params![
                asset_id as i64,
                keys.enc_keys.iter().copied().collect::<Vec<_>>().encode(),
                keys.mediators.iter().copied().collect::<Vec<_>>().encode()
            ],
        )?;
        Ok(())
    }

    /// `OwnerAssets::insert`.
    pub fn insert_owner_asset(&self, identity_id: i64, asset_id: AssetId) -> ChainResult<()> {
        self.conn.execute(
            "INSERT INTO owner_assets (identity_id, asset_id) VALUES (?1, ?2)",
            params![identity_id, asset_id as i64],
        )?;
        Ok(())
    }

    /// `AssetFrozen::set` (`None` clears the flag).
    pub fn set_asset_frozen(&self, asset_id: AssetId, origin: Option<&str>) -> ChainResult<()> {
        match origin {
            None => {
                self.conn.execute(
                    "DELETE FROM asset_frozen WHERE asset_id = ?1",
                    params![asset_id as i64],
                )?;
            }
            Some(origin) => {
                self.conn.execute(
                    "INSERT INTO asset_frozen (asset_id, freeze_origin) VALUES (?1, ?2)
                     ON CONFLICT(asset_id) DO UPDATE SET freeze_origin = ?2",
                    params![asset_id as i64, origin],
                )?;
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------- fee pool

    /// Balance of the pallet fee account (`CONFIDENTIAL_ASSETS_FEE_ID`).
    pub fn fee_pool_balance(&self) -> ChainResult<u64> {
        from_i64(self.row_i64("SELECT balance FROM fee_pool WHERE id = 1", [])?)
    }

    pub fn adjust_fee_pool(&self, delta: i64) -> ChainResult<u64> {
        let current = i64::try_from(self.fee_pool_balance()?)
            .map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))?;
        let updated = current
            .checked_add(delta)
            .ok_or(ChainFailure::Error(ChainError::AmountOverflow))?;
        if updated < 0 {
            return Err(ChainFailure::Error(ChainError::InsufficientBalance));
        }
        self.conn.execute(
            "UPDATE fee_pool SET balance = ?1 WHERE id = 1",
            params![updated],
        )?;
        Ok(updated as u64)
    }

    /// Write a consistent copy of the database to `path`. Used to keep a recording session's
    /// chain snapshot next to its corpus, separate from the main `--database`.
    ///
    /// `VACUUM INTO` cannot run inside a transaction, so this is called after a command has
    /// committed or rolled back.
    pub fn snapshot_to(&self, path: &Path) -> ChainResult<()> {
        if self.tx_depth.get() != 0 {
            return Err(ChainFailure::Internal(
                "cannot snapshot the database inside a transaction".into(),
            ));
        }
        if path.exists() {
            std::fs::remove_file(path)?;
        }
        let path = path.to_string_lossy().into_owned();
        self.conn.execute("VACUUM INTO ?1", params![path])?;
        Ok(())
    }

    // ---------------------------------------------------------------- generic row readers

    pub fn row_i64<P: rusqlite::Params>(&self, sql: &str, p: P) -> ChainResult<i64> {
        self.conn
            .query_row(sql, p, |row| row.get(0))
            .optional()
            .map_err(ChainFailure::from)
            .map(|v| v.unwrap_or(0))
    }

    pub fn row_text<P: rusqlite::Params>(&self, sql: &str, p: P) -> ChainResult<Option<String>> {
        self.conn
            .query_row(sql, p, |row| row.get::<_, String>(0))
            .optional()
            .map_err(ChainFailure::from)
    }

    /// Number of recorded dispatches — used to derive the CLI's deterministic RNG state so
    /// successive runs of the same scenario draw fresh (but reproducible) key material.
    pub fn tx_count(&self) -> ChainResult<u64> {
        self.row_i64("SELECT COUNT(*) FROM tx_log", [])
            .map(|v| v.max(0) as u64)
    }

    /// Prover-side row counts (also mixed into the derived seed).
    pub fn prover_progress(&self) -> ChainResult<u64> {
        let accounts = self.row_i64("SELECT COUNT(*) FROM accounts", [])?;
        let identities = self.row_i64("SELECT COUNT(*) FROM identities", [])?;
        Ok((accounts.max(0) + identities.max(0)) as u64)
    }
}

const SCHEMA_TABLES: &[&str] = &[
    "chain_state",
    "tree_state",
    "tree_leaves",
    "tree_inner_nodes",
    "tree_roots",
    "tree_nullifiers",
    // Drop children before parents: `accounts`/`account_did` reference `identities`, and
    // SQLite's bundled build enforces foreign keys.
    "accounts",
    "account_did",
    "identities",
    "did_accounts",
    "encryption_key_did",
    "account_encryption_key",
    "encryption_key_account",
    "fee_account_did",
    "required_claims",
    "claims",
    "shared_key_recipients",
    "assets",
    "asset_keys",
    "asset_frozen",
    "owner_assets",
    "account_asset_registrations",
    "settlement_state",
    "settlement_aliases",
    "chain_config",
    "settlement_memo",
    "settlement_legs",
    "settlement_leg_count",
    "settlement_pending_affirmations",
    "settlement_pending_finalizations",
    "leg_affirmation_status",
    "leg_mediators",
    "fee_pool",
    "tx_log",
    "event_log",
    // Prover state (no pallet equivalent): the CLI must remember what the prover used.
    "prover_account_states",
    "prover_fee_account_states",
    "proof_state_index",
    "host_enc_keys",
];

const SCHEMA: &str = "
CREATE TABLE IF NOT EXISTS host_enc_keys (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    owner TEXT NOT NULL,
    enc_key BLOB UNIQUE NOT NULL,
    secret BLOB NOT NULL
);
CREATE TABLE IF NOT EXISTS proof_state_index (
    nullifier BLOB PRIMARY KEY,
    account_key BLOB NOT NULL,
    asset_id INTEGER NOT NULL
);
CREATE TABLE IF NOT EXISTS chain_state (
    id INTEGER PRIMARY KEY CHECK (id = 1),
    block_number INTEGER NOT NULL,
    moment INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS tree_state (
    tree TEXT NOT NULL PRIMARY KEY,
    height INTEGER NOT NULL,
    next_leaf_index INTEGER NOT NULL,
    last_committed_leaf_index INTEGER NOT NULL,
    last_pruned_block INTEGER NOT NULL,
    last_update_moment INTEGER NOT NULL,
    current_root BLOB
);

CREATE TABLE IF NOT EXISTS tree_leaves (
    tree TEXT NOT NULL,
    leaf_index INTEGER NOT NULL,
    leaf_data BLOB NOT NULL,
    PRIMARY KEY (tree, leaf_index)
);

CREATE TABLE IF NOT EXISTS tree_inner_nodes (
    tree TEXT NOT NULL,
    location BLOB NOT NULL,
    node_data BLOB NOT NULL,
    PRIMARY KEY (tree, location)
);

CREATE TABLE IF NOT EXISTS tree_roots (
    tree TEXT NOT NULL,
    block_number INTEGER NOT NULL,
    height INTEGER NOT NULL,
    moment INTEGER NOT NULL,
    root_data BLOB NOT NULL,
    PRIMARY KEY (tree, block_number)
);

CREATE TABLE IF NOT EXISTS tree_nullifiers (
    tree TEXT NOT NULL,
    nullifier BLOB NOT NULL,
    PRIMARY KEY (tree, nullifier)
);

CREATE TABLE IF NOT EXISTS identities (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL UNIQUE,
    did BLOB NOT NULL UNIQUE
);

CREATE TABLE IF NOT EXISTS accounts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    identity_id INTEGER NOT NULL REFERENCES identities(id),
    name TEXT NOT NULL,
    key_seed TEXT NOT NULL,
    account_key BLOB NOT NULL,
    enc_key BLOB NOT NULL,
    UNIQUE (identity_id, name)
);

CREATE TABLE IF NOT EXISTS account_did (
    account_key BLOB NOT NULL PRIMARY KEY,
    identity_id INTEGER NOT NULL REFERENCES identities(id)
);

CREATE TABLE IF NOT EXISTS did_accounts (
    identity_id INTEGER NOT NULL,
    account_key BLOB NOT NULL,
    PRIMARY KEY (identity_id, account_key)
);

CREATE TABLE IF NOT EXISTS encryption_key_did (
    enc_key BLOB NOT NULL PRIMARY KEY,
    identity_id INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS account_encryption_key (
    account_key BLOB NOT NULL PRIMARY KEY,
    enc_key BLOB NOT NULL
);

CREATE TABLE IF NOT EXISTS encryption_key_account (
    enc_key BLOB NOT NULL PRIMARY KEY,
    account_key BLOB NOT NULL
);

CREATE TABLE IF NOT EXISTS fee_account_did (
    account_key BLOB NOT NULL PRIMARY KEY,
    identity_id INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS required_claims (
    role TEXT NOT NULL PRIMARY KEY,
    claim BLOB NOT NULL,
    trusted_issuers BLOB NOT NULL
);

CREATE TABLE IF NOT EXISTS claims (
    identity_id INTEGER NOT NULL,
    issuer_identity_id INTEGER NOT NULL,
    claim BLOB NOT NULL,
    expiry_moment INTEGER NOT NULL,
    PRIMARY KEY (identity_id, issuer_identity_id, claim)
);

CREATE TABLE IF NOT EXISTS shared_key_recipients (
    enc_key BLOB NOT NULL,
    recipient BLOB NOT NULL,
    PRIMARY KEY (enc_key, recipient)
);

CREATE TABLE IF NOT EXISTS assets (
    asset_id INTEGER PRIMARY KEY,
    name TEXT NOT NULL,
    symbol TEXT NOT NULL,
    decimals INTEGER NOT NULL,
    data BLOB,
    issuer_identity_id INTEGER NOT NULL,
    total_supply INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS asset_keys (
    asset_id INTEGER PRIMARY KEY,
    enc_keys BLOB NOT NULL,
    mediators BLOB NOT NULL
);

CREATE TABLE IF NOT EXISTS asset_frozen (
    asset_id INTEGER PRIMARY KEY,
    freeze_origin TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS owner_assets (
    identity_id INTEGER NOT NULL,
    asset_id INTEGER NOT NULL,
    PRIMARY KEY (identity_id, asset_id)
);

CREATE TABLE IF NOT EXISTS account_asset_registrations (
    account_key BLOB NOT NULL,
    asset_id INTEGER NOT NULL,
    PRIMARY KEY (account_key, asset_id)
);

CREATE TABLE IF NOT EXISTS settlement_state (
    settlement_ref BLOB NOT NULL PRIMARY KEY,
    status TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS settlement_aliases (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    settlement_ref BLOB NOT NULL UNIQUE
);

CREATE TABLE IF NOT EXISTS chain_config (
    key TEXT NOT NULL PRIMARY KEY,
    value TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS settlement_memo (
    settlement_ref BLOB NOT NULL PRIMARY KEY,
    memo BLOB NOT NULL
);

CREATE TABLE IF NOT EXISTS settlement_legs (
    settlement_ref BLOB NOT NULL,
    leg_id INTEGER NOT NULL,
    leg_enc BLOB NOT NULL,
    PRIMARY KEY (settlement_ref, leg_id)
);

CREATE TABLE IF NOT EXISTS settlement_leg_count (
    settlement_ref BLOB NOT NULL PRIMARY KEY,
    leg_count INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS settlement_pending_affirmations (
    settlement_ref BLOB NOT NULL PRIMARY KEY,
    pending INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS settlement_pending_finalizations (
    settlement_ref BLOB NOT NULL PRIMARY KEY,
    pending INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS leg_affirmation_status (
    settlement_ref BLOB NOT NULL,
    leg_id INTEGER NOT NULL,
    party TEXT NOT NULL,
    status TEXT NOT NULL,
    PRIMARY KEY (settlement_ref, leg_id, party)
);

CREATE TABLE IF NOT EXISTS leg_mediators (
    settlement_ref BLOB NOT NULL,
    leg_id INTEGER NOT NULL,
    mediators BLOB NOT NULL,
    PRIMARY KEY (settlement_ref, leg_id)
);

CREATE TABLE IF NOT EXISTS fee_pool (
    id INTEGER PRIMARY KEY CHECK (id = 1),
    balance INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS tx_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    block_number INTEGER NOT NULL,
    moment INTEGER NOT NULL,
    call TEXT NOT NULL,
    outcome TEXT NOT NULL,
    error TEXT
);

CREATE TABLE IF NOT EXISTS event_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    tx_id INTEGER NOT NULL,
    block_number INTEGER NOT NULL,
    call TEXT NOT NULL,
    event TEXT NOT NULL,
    detail TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS prover_account_states (
    account_key BLOB NOT NULL,
    asset_id INTEGER NOT NULL,
    state_data BLOB NOT NULL,
    PRIMARY KEY (account_key, asset_id)
);

CREATE TABLE IF NOT EXISTS prover_fee_account_states (
    account_key BLOB NOT NULL,
    asset_id INTEGER NOT NULL,
    state_data BLOB,
    pending_state_data BLOB,
    PRIMARY KEY (account_key, asset_id)
);
";
