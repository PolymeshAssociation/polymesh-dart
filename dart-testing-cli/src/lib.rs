use anyhow::{anyhow, Result};
use codec::{Decode, Encode};
use rand_core::{CryptoRng, RngCore};
use rusqlite::{params, Connection};
use serde::{Deserialize, Serialize};
use std::fs::File;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use polymesh_dart::curve_tree::{get_account_curve_tree_parameters, CurveTreeRoot};
use polymesh_dart::*;

mod sqlite_curve_tree;
use sqlite_curve_tree::{AccountCurveTree, AccountRootHistory, AssetCurveTree, AssetRootHistory};

/// The affirmation status for each party in a DART settlement leg.
#[derive(Copy, Clone, Encode, Decode, Debug, PartialEq, Eq)]
pub enum AffirmationStatus {
    /// The leg is pending affirmation.
    Pending,
    /// The leg has been affirmed by the sender, receiver, and mediator.
    Affirmed,
    /// The leg has been rejected by one party.
    Rejected,
    /// The leg has been finalized by all parties.
    Finalized,
}

impl AffirmationStatus {
    /// Merge two affirmation statuses together.
    pub fn merge(self, other: AffirmationStatus) -> Result<AffirmationStatus> {
        use AffirmationStatus::*;
        match (self, other) {
            (Pending, Pending) => Ok(Pending),
            (Pending, Affirmed) => Ok(Pending),
            (Pending, Rejected) => Ok(Rejected),
            (Pending, Finalized) => Err(anyhow!("Cannot go from pending to finalized")),

            (Affirmed, Pending) => Ok(Pending),
            (Affirmed, Affirmed) => Ok(Affirmed),
            (Affirmed, Rejected) => Ok(Rejected),
            (Affirmed, Finalized) => Ok(Affirmed),

            (Rejected, Pending) => Ok(Rejected),
            (Rejected, Affirmed) => Ok(Rejected),
            (Rejected, Rejected) => Ok(Rejected),
            (Rejected, Finalized) => Err(anyhow!("Cannot go from rejected to finalized")),

            (Finalized, Pending) => Err(anyhow!("Cannot go from finalized to pending")),
            (Finalized, Affirmed) => Ok(Affirmed),
            (Finalized, Rejected) => Err(anyhow!("Cannot go from finalized to rejected")),
            (Finalized, Finalized) => Ok(Finalized),
        }
    }

    pub fn from_str(s: &str) -> Result<Self> {
        match s {
            "Pending" => Ok(AffirmationStatus::Pending),
            "Affirmed" => Ok(AffirmationStatus::Affirmed),
            "Rejected" => Ok(AffirmationStatus::Rejected),
            "Finalized" => Ok(AffirmationStatus::Finalized),
            _ => Err(anyhow!("Invalid affirmation status: {}", s)),
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            AffirmationStatus::Pending => "Pending",
            AffirmationStatus::Affirmed => "Affirmed",
            AffirmationStatus::Rejected => "Rejected",
            AffirmationStatus::Finalized => "Finalized",
        }
    }
}

/// Settlement status for a DART settlement.
#[derive(Copy, Clone, Encode, Decode, Debug, PartialEq, Eq)]
pub enum SettlementStatus {
    Pending,
    Executed,
    Rejected,
    Finalized,
}

impl SettlementStatus {
    pub fn from_str(s: &str) -> Result<Self> {
        match s {
            "Pending" => Ok(SettlementStatus::Pending),
            "Executed" => Ok(SettlementStatus::Executed),
            "Rejected" => Ok(SettlementStatus::Rejected),
            "Finalized" => Ok(SettlementStatus::Finalized),
            _ => Err(anyhow!("Invalid settlement status: {}", s)),
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            SettlementStatus::Pending => "Pending",
            SettlementStatus::Executed => "Executed",
            SettlementStatus::Rejected => "Rejected",
            SettlementStatus::Finalized => "Finalized",
        }
    }
}

#[derive(Debug)]
pub enum ProofAction {
    /// Write proof to file instead of applying
    GenerateOnly(File),
    /// Read proof from file and apply
    ApplyOnly {
        /// Serialized proof data to apply.
        proof: Vec<u8>,
        /// If true, only verify the proof without applying it.
        dry_run: bool,
    },
    /// Generate and apply proof
    GenerateAndApply {
        /// If true, only generate and verify the proof without applying it.
        dry_run: bool,
    },
}

impl ProofAction {
    pub fn new(write: Option<PathBuf>, read: Option<PathBuf>, dry_run: bool) -> Result<Self> {
        match (write, read) {
            (Some(write_path), None) => {
                let file = File::create(write_path)?;
                Ok(ProofAction::GenerateOnly(file))
            }
            (None, Some(read_path)) => {
                let proof = std::fs::read(read_path)?;
                Ok(ProofAction::ApplyOnly { proof, dry_run })
            }
            (Some(_), Some(_)) => Err(anyhow!("Cannot specify both write and read paths")),
            (None, None) => Ok(ProofAction::GenerateAndApply { dry_run }),
        }
    }

    pub fn get_proof<T: Decode>(&self) -> Result<Option<T>> {
        match self {
            ProofAction::GenerateOnly(_) => Ok(None), // No proof generated yet
            ProofAction::ApplyOnly { proof, .. } => T::decode(&mut proof.as_slice())
                .map(Some)
                .map_err(|e| anyhow!("Failed to decode proof: {}", e)),
            ProofAction::GenerateAndApply { .. } => Ok(None), // No proof generated yet
        }
    }

    pub fn save_proof<T: Encode>(&mut self, proof: &T) -> Result<()> {
        match self {
            ProofAction::GenerateOnly(file) => {
                file.write_all(&proof.encode())?;
                Ok(())
            }
            ProofAction::ApplyOnly { .. } => Ok(()),
            ProofAction::GenerateAndApply { .. } => Ok(()),
        }
    }

    pub fn apply_proof(&self) -> bool {
        match self {
            ProofAction::ApplyOnly { .. } | ProofAction::GenerateAndApply { .. } => true,
            ProofAction::GenerateOnly(_) => false,
        }
    }

    pub fn is_dry_run(&self) -> bool {
        match self {
            ProofAction::ApplyOnly { dry_run, .. } => *dry_run,
            ProofAction::GenerateAndApply { dry_run } => *dry_run,
            ProofAction::GenerateOnly(_) => false, // No dry run for generation
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignerInfo {
    pub id: i64,
    pub name: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DartAccountInfo {
    pub id: i64,
    pub signer_id: i64,
    pub name: String,
    pub account_key: Vec<u8>,    // SCALE encoded AccountPublicKey
    pub encryption_key: Vec<u8>, // SCALE encoded EncryptionPublicKey
    pub key_seed: String,        // Random seed used to generate AccountKeys
}

impl DartAccountInfo {
    pub fn account_public_keys(&self) -> Result<AccountPublicKeys> {
        let acct = AccountPublicKey::decode(&mut self.account_key.as_slice())?;
        let enc = EncryptionPublicKey::decode(&mut self.encryption_key.as_slice())?;
        Ok(AccountPublicKeys { acct, enc })
    }

    pub fn account_keys(&self) -> Result<AccountKeys> {
        Ok(AccountKeys::from_seed(&self.key_seed)?)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssetInfo {
    pub id: i64,
    pub asset_id: AssetId,
    pub issuer_signer_id: i64,
    pub auditors: Vec<u8>,  // Serialized Vec<EncryptionPublicKey>
    pub mediators: Vec<u8>, // Serialized Vec<EncryptionPublicKey>
    pub total_supply: Balance,
}

impl AssetInfo {
    pub fn auditors(&self) -> Result<Vec<EncryptionPublicKey>> {
        Ok(Decode::decode(&mut self.auditors.as_slice())?)
    }

    pub fn mediators(&self) -> Result<Vec<EncryptionPublicKey>> {
        Ok(Decode::decode(&mut self.mediators.as_slice())?)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SettlementInfo {
    pub id: i64,
    pub settlement_id: SettlementId,
    pub status: String, // "Pending", "Executed", "Rejected", "Finalized"
    pub created_by_signer_id: Option<i64>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SettlementLegInfo {
    pub id: i64,
    pub settlement_db_id: i64,
    pub leg_index: LegId,
    pub encrypted_leg: Vec<u8>, // Serialized LegEncrypted
    pub sender_status: String,
    pub receiver_status: String,
    pub mediator_status: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccountAssetStateInfo {
    pub id: i64,
    pub account_db_id: i64,
    pub asset_db_id: i64,
    pub state_data: Vec<u8>, // Serialized AccountAssetState
}

impl AccountAssetStateInfo {
    pub fn get_state(&self, account_info: &DartAccountInfo) -> Result<AccountAssetState> {
        let account = account_info.account_public_keys()?;
        let db_state = AccountAssetStateDb::decode(&mut self.state_data.as_slice())?;
        Ok(AccountAssetState {
            account: account.acct,
            asset_id: db_state.asset_id,
            current_state: db_state.current_state,
            current_state_commitment: db_state.current_state_commitment,
            current_tx_id: db_state.current_tx_id,
            pending_state: db_state.pending_state,
        })
    }
}

#[derive(Debug, Clone, Encode, Decode)]
pub struct AccountAssetStateDb {
    pub asset_id: AssetId,
    pub current_state: AccountState,
    pub current_state_commitment: AccountStateCommitment,
    pub current_tx_id: u64,
    pub pending_state: Option<(AccountState, AccountStateCommitment)>,
}

impl AccountAssetStateDb {
    pub fn from_state(state: AccountAssetState) -> Self {
        Self {
            asset_id: state.asset_id,
            current_state: state.current_state,
            current_state_commitment: state.current_state_commitment,
            current_tx_id: state.current_tx_id,
            pending_state: state.pending_state,
        }
    }
}

pub struct DartTestingDb {
    conn: Arc<Connection>,
    asset_tree: AssetCurveTree,
    asset_roots: AssetRootHistory,
    account_tree: AccountCurveTree,
    account_roots: AccountRootHistory,
}

impl DartTestingDb {
    pub fn new<P: AsRef<Path>>(db_path: P) -> Result<Self> {
        let conn = Arc::new(Connection::open(db_path)?);

        let asset_tree = AssetCurveTree::new(conn.clone())?;
        let account_tree = AccountCurveTree::new(conn.clone())?;
        let asset_roots = AssetRootHistory::new(conn.clone());
        let account_roots = AccountRootHistory::new(conn.clone());

        let db = Self {
            conn,
            asset_roots,
            asset_tree,
            account_roots,
            account_tree,
        };

        db.create_tables()?;

        Ok(db)
    }

    pub fn initialize_db(&self) -> Result<()> {
        self.drop_tables()?;
        self.create_tables()?;

        Ok(())
    }

    fn drop_tables(&self) -> Result<()> {
        let tables = [
            "pending_account_commitments",
            "account_asset_states",
            "settlement_legs",
            "settlements",
            "account_root_history",
            "asset_root_history",
            "asset_registered_accounts",
            "account_inner_nodes",
            "asset_inner_nodes",
            "account_leaves",
            "asset_leaves",
            "assets",
            "dart_accounts",
            "signers",
        ];

        for table in &tables {
            self.conn
                .execute(&format!("DROP TABLE IF EXISTS {}", table), [])?;
        }
        Ok(())
    }

    fn create_tables(&self) -> Result<()> {
        // Signers table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS signers (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT UNIQUE NOT NULL
            )",
            [],
        )?;

        // Dart accounts table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS dart_accounts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                signer_id INTEGER NOT NULL,
                name TEXT NOT NULL,
                account_key BLOB NOT NULL,
                encryption_key BLOB NOT NULL,
                key_seed TEXT NOT NULL,
                FOREIGN KEY(signer_id) REFERENCES signers(id),
                UNIQUE(signer_id, name)
            )",
            [],
        )?;

        // Assets table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS assets (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                asset_id INTEGER NOT NULL UNIQUE,
                issuer_signer_id INTEGER NOT NULL,
                auditors BLOB NOT NULL,
                mediators BLOB NOT NULL,
                total_supply INTEGER NOT NULL DEFAULT 0,
                FOREIGN KEY(issuer_signer_id) REFERENCES signers(id)
            )",
            [],
        )?;

        // Asset leaves table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS asset_leaves (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                leaf_index INTEGER NOT NULL UNIQUE,
                leaf_data BLOB NOT NULL
            )",
            [],
        )?;

        // Account leaves table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS account_leaves (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                leaf_index INTEGER NOT NULL UNIQUE,
                leaf_data BLOB NOT NULL
            )",
            [],
        )?;

        // Asset tree inner nodes table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS asset_inner_nodes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                location BLOB NOT NULL UNIQUE,
                node_data BLOB NOT NULL
            )",
            [],
        )?;

        // Account tree inner nodes table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS account_inner_nodes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                location BLOB NOT NULL UNIQUE,
                node_data BLOB NOT NULL
            )",
            [],
        )?;

        // Asset registered accounts table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS asset_registered_accounts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                account_db_id INTEGER NOT NULL,
                asset_db_id INTEGER NOT NULL,
                FOREIGN KEY(account_db_id) REFERENCES dart_accounts(id),
                FOREIGN KEY(asset_db_id) REFERENCES assets(id),
                UNIQUE(account_db_id, asset_db_id)
            )",
            [],
        )?;

        // Asset tree roots table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS asset_root_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                block_number INTEGER NOT NULL,
                root_data BLOB NOT NULL
            )",
            [],
        )?;

        // Account tree roots table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS account_root_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                block_number INTEGER NOT NULL,
                root_data BLOB NOT NULL
            )",
            [],
        )?;

        // Settlements table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS settlements (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                settlement_id INTEGER NOT NULL UNIQUE,
                status TEXT NOT NULL DEFAULT 'Pending',
                created_by_signer_id INTEGER,
                FOREIGN KEY(created_by_signer_id) REFERENCES signers(id)
            )",
            [],
        )?;

        // Settlement legs table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS settlement_legs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                settlement_db_id INTEGER NOT NULL,
                leg_index INTEGER NOT NULL,
                encrypted_leg BLOB NOT NULL,
                sender_status TEXT NOT NULL DEFAULT 'Pending',
                receiver_status TEXT NOT NULL DEFAULT 'Pending',
                mediator_status TEXT,
                FOREIGN KEY(settlement_db_id) REFERENCES settlements(id),
                UNIQUE(settlement_db_id, leg_index)
            )",
            [],
        )?;

        // Account asset states table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS account_asset_states (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                account_db_id INTEGER NOT NULL,
                asset_db_id INTEGER NOT NULL,
                state_data BLOB NOT NULL,
                FOREIGN KEY(account_db_id) REFERENCES dart_accounts(id),
                FOREIGN KEY(asset_db_id) REFERENCES assets(id),
                UNIQUE(account_db_id, asset_db_id)
            )",
            [],
        )?;

        // Pending account commitments table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS pending_account_commitments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                commitment_data BLOB NOT NULL
            )",
            [],
        )?;

        // Account nullifiers table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS account_nullifiers (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                nullifier_data BLOB NOT NULL UNIQUE
            )",
            [],
        )?;

        Ok(())
    }

    /// Get the next block number from the database.
    /// This is used to track the current block number for root history.
    pub fn get_next_block_number(&self) -> Result<BlockNumber> {
        // query both of the root history tables for the maximum block number
        let asset_max: i64 = self.conn.query_row(
            "SELECT COALESCE(MAX(block_number), 0) FROM asset_root_history",
            [],
            |row| row.get(0),
        )?;
        let account_max: i64 = self.conn.query_row(
            "SELECT COALESCE(MAX(block_number), 0) FROM account_root_history",
            [],
            |row| row.get(0),
        )?;
        // The next block number is the maximum of both tables + 1
        let next_block = std::cmp::max(asset_max, account_max) + 1;
        Ok(next_block as BlockNumber)
    }

    // Signer operations
    pub fn create_signer(&mut self, name: &str) -> Result<SignerInfo> {
        self.conn
            .execute("INSERT INTO signers (name) VALUES (?1)", params![name])?;

        let id = self.conn.last_insert_rowid();
        Ok(SignerInfo {
            id,
            name: name.to_string(),
        })
    }

    pub fn get_signer_by_name(&self, name: &str) -> Result<SignerInfo> {
        let mut stmt = self
            .conn
            .prepare("SELECT id, name FROM signers WHERE name = ?1")?;
        let signer = stmt.query_row(params![name], |row| {
            Ok(SignerInfo {
                id: row.get(0)?,
                name: row.get(1)?,
            })
        })?;
        Ok(signer)
    }

    // Dart account operations
    pub fn create_dart_account<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
    ) -> Result<DartAccountInfo> {
        let signer = self.get_signer_by_name(signer_name)?;

        // Generate a random seed for account keys
        let mut key_seed = [0u8; 32];
        rng.fill_bytes(&mut key_seed);
        let key_seed = hex::encode(key_seed);

        let account_keys = AccountKeys::from_seed(&key_seed)?;
        let public_keys = account_keys.public_keys();

        let account_key_bytes = public_keys.acct.encode();
        let encryption_key_bytes = public_keys.enc.encode();

        self.conn.execute(
            "INSERT INTO dart_accounts (signer_id, name, account_key, encryption_key, key_seed) 
             VALUES (?1, ?2, ?3, ?4, ?5)",
            params![
                signer.id,
                account_name,
                account_key_bytes,
                encryption_key_bytes,
                key_seed
            ],
        )?;

        let id = self.conn.last_insert_rowid();
        Ok(DartAccountInfo {
            id,
            signer_id: signer.id,
            name: account_name.to_string(),
            account_key: account_key_bytes,
            encryption_key: encryption_key_bytes,
            key_seed,
        })
    }

    pub fn get_dart_account(
        &self,
        signer_name: &str,
        account_name: &str,
    ) -> Result<DartAccountInfo> {
        log::debug!(
            "Getting Dart account for signer '{}' and account '{}'",
            signer_name,
            account_name
        );
        let mut stmt = self.conn.prepare(
            "SELECT da.id, da.signer_id, da.name, da.account_key, da.encryption_key, da.key_seed
             FROM dart_accounts da
             JOIN signers s ON da.signer_id = s.id
             WHERE s.name = ?1 AND da.name = ?2",
        )?;

        let account = stmt.query_row(params![signer_name, account_name], |row| {
            Ok(DartAccountInfo {
                id: row.get(0)?,
                signer_id: row.get(1)?,
                name: row.get(2)?,
                account_key: row.get(3)?,
                encryption_key: row.get(4)?,
                key_seed: row.get(5)?,
            })
        })?;
        Ok(account)
    }

    pub fn get_account_public_keys(
        &self,
        account_info: &DartAccountInfo,
    ) -> Result<AccountPublicKeys> {
        let acct = AccountPublicKey::decode(&mut account_info.account_key.as_slice())?;
        let enc = EncryptionPublicKey::decode(&mut account_info.encryption_key.as_slice())?;
        Ok(AccountPublicKeys { acct, enc })
    }

    // Asset operations
    pub fn create_asset(
        &mut self,
        issuer_signer_name: &str,
        auditors: &[EncryptionPublicKey],
        mediators: &[EncryptionPublicKey],
    ) -> Result<AssetInfo> {
        let signer = self.get_signer_by_name(issuer_signer_name)?;

        // Get next asset ID
        let asset_id: AssetId = self.conn.query_row(
            "SELECT COALESCE(MAX(asset_id), -1) + 1 FROM assets",
            [],
            |row| row.get(0),
        )?;

        let auditors_bytes = auditors.encode();
        let mediators_bytes = mediators.encode();

        self.conn.execute(
            "INSERT INTO assets (asset_id, issuer_signer_id, auditors, mediators, total_supply) 
             VALUES (?1, ?2, ?3, ?4, 0)",
            params![asset_id, signer.id, auditors_bytes, mediators_bytes],
        )?;

        let id = self.conn.last_insert_rowid();

        // Update the asset tree
        let asset_state = self.create_asset_state(asset_id, auditors, mediators)?;
        let asset_data = asset_state.asset_data()?;
        let leaf_index = asset_id as _;
        self.asset_tree
            .update_leaf(leaf_index, asset_data.commitment.into())?;

        Ok(AssetInfo {
            id,
            asset_id,
            issuer_signer_id: signer.id,
            auditors: auditors_bytes,
            mediators: mediators_bytes,
            total_supply: 0,
        })
    }

    fn create_asset_state(
        &self,
        asset_id: AssetId,
        auditors: &[EncryptionPublicKey],
        mediators: &[EncryptionPublicKey],
    ) -> Result<AssetState> {
        Ok(AssetState::new(asset_id, auditors, mediators))
    }

    pub fn get_asset_by_id(&self, asset_id: AssetId) -> Result<AssetInfo> {
        let mut stmt = self.conn.prepare(
            "SELECT id, asset_id, issuer_signer_id, auditors, mediators, total_supply FROM assets WHERE asset_id = ?1"
        )?;

        let asset = stmt.query_row(params![asset_id], |row| {
            Ok(AssetInfo {
                id: row.get(0)?,
                asset_id: row.get(1)?,
                issuer_signer_id: row.get(2)?,
                auditors: row.get(3)?,
                mediators: row.get(4)?,
                total_supply: row.get(5)?,
            })
        })?;
        Ok(asset)
    }

    // End block operation
    pub fn end_block(&mut self) -> Result<()> {
        // Process all pending account commitments
        let mut stmt = self
            .conn
            .prepare("SELECT commitment_data FROM pending_account_commitments ORDER BY id")?;

        let commitment_rows = stmt.query_map([], |row| Ok(row.get::<_, Vec<u8>>(0)?))?;

        // Insert all pending commitments into account tree
        for commitment_data in commitment_rows {
            let commitment_data = commitment_data?;
            let commitment = AccountStateCommitment::decode(&mut commitment_data.as_slice())?;
            self.account_tree.insert_leaf(commitment.as_leaf_value()?)?;
        }

        // Clear pending commitments
        self.conn
            .execute("DELETE FROM pending_account_commitments", [])?;

        // Get current tree roots
        let asset_root = CurveTreeRoot::new(&self.asset_tree.root_node()?)?;
        let account_root = CurveTreeRoot::new(&self.account_tree.root_node()?)?;

        // Store roots in database
        let block_number = self.get_next_block_number()?;
        self.asset_roots.add_root(block_number, &asset_root)?;
        self.account_roots.add_root(block_number, &account_root)?;

        Ok(())
    }

    fn append_account_commitment(&mut self, commitment: AccountStateCommitment) -> Result<()> {
        // Store commitment in pending table instead of directly inserting into tree
        let commitment_data = commitment.encode();
        self.conn.execute(
            "INSERT INTO pending_account_commitments (commitment_data) VALUES (?1)",
            params![commitment_data],
        )?;

        Ok(())
    }

    fn ensure_nullifier_unique(&self, nullifier: &AccountStateNullifier) -> Result<()> {
        let nullifier_data = nullifier.encode();
        let count: i64 = self.conn.query_row(
            "SELECT COUNT(*) FROM account_nullifiers WHERE nullifier_data = ?1",
            params![nullifier_data],
            |row| row.get(0),
        )?;

        if count > 0 {
            return Err(anyhow!("Nullifier has already been used"));
        }
        Ok(())
    }

    fn add_nullifier(&mut self, nullifier: AccountStateNullifier) -> Result<()> {
        let nullifier_data = nullifier.encode();
        self.conn.execute(
            "INSERT INTO account_nullifiers (nullifier_data) VALUES (?1)",
            params![nullifier_data],
        )?;
        Ok(())
    }

    // Asset registration operations
    pub fn register_account_with_asset<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        asset_id: AssetId,
        mut proof_action: ProofAction,
    ) -> Result<()> {
        let account_info = self.get_dart_account(signer_name, account_name)?;
        let asset_info = self.get_asset_by_id(asset_id)?;

        // Check if already registered
        let count: i64 = self.conn.query_row(
            "SELECT COUNT(*) FROM asset_registered_accounts WHERE account_db_id = ?1 AND asset_db_id = ?2",
            params![account_info.id, asset_info.id],
            |row| row.get(0)
        )?;

        if count > 0 {
            return Err(anyhow!(
                "Account {} is already registered with asset {}",
                account_name,
                asset_id
            ));
        }
        let params = get_account_curve_tree_parameters();

        let (proof, mut asset_state) = if let Some(proof) = proof_action.get_proof()? {
            // Get and update account asset state
            let asset_state = self.get_account_asset_state(&account_info, asset_id)?;
            (proof, asset_state)
        } else {
            let account_keys = account_info.account_keys()?;
            // Create registration proof and initial state.
            let (proof, asset_state) = AccountAssetRegistrationProof::new(
                rng,
                &account_keys.acct,
                asset_id,
                0,
                signer_name.as_bytes(),
                params,
            )?;

            // Update the account state with the pending state change.
            self.update_account_asset_state(&account_info, &asset_state)?;

            (proof, asset_state)
        };

        // If proof action is to generate only, save proof and return
        if !proof_action.apply_proof() {
            proof_action.save_proof(&proof)?;
            return Ok(());
        }

        // Verify the proof
        proof.verify(signer_name.as_bytes(), params, rng)?;

        if proof_action.is_dry_run() {
            // If dry run, just verify and return
            return Ok(());
        }

        // Register in database
        self.conn.execute(
            "INSERT INTO asset_registered_accounts (account_db_id, asset_db_id) VALUES (?1, ?2)",
            params![account_info.id, asset_info.id],
        )?;

        // Store the account asset state
        asset_state.commit_pending_state()?;
        self.update_account_asset_state(&account_info, &asset_state)?;

        // Append the account commitment to the account tree
        self.append_account_commitment(asset_state.current_state_commitment)?;

        Ok(())
    }

    pub fn mint_assets<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        issuer_signer_name: &str,
        account_name: &str,
        asset_id: AssetId,
        amount: Balance,
        mut proof_action: ProofAction,
    ) -> Result<()> {
        let account_info = self.get_dart_account(issuer_signer_name, account_name)?;
        let mut asset_info = self.get_asset_by_id(asset_id)?;

        // Verify issuer owns the asset
        if asset_info.issuer_signer_id != account_info.signer_id {
            return Err(anyhow!(
                "Signer {} is not the issuer of asset {}",
                issuer_signer_name,
                asset_id
            ));
        }

        // Get and update account asset state
        let mut asset_state = self.get_account_asset_state(&account_info, asset_id)?;

        let proof = if let Some(proof) = proof_action.get_proof()? {
            proof
        } else {
            let account_keys = account_info.account_keys()?;
            // Create minting proof
            let proof = AssetMintingProof::new(
                rng,
                &account_keys.acct,
                &mut asset_state,
                &self.account_tree,
                amount,
            )?;

            // Update the account state with the pending state change.
            self.update_account_asset_state(&account_info, &asset_state)?;

            proof
        };

        // If proof action is to generate only, save proof and return
        if !proof_action.apply_proof() {
            proof_action.save_proof(&proof)?;
            return Ok(());
        }

        // Verify the proof and handle the account state update.
        self.handle_account_state_update_proof(
            &account_info,
            &mut asset_state,
            &proof,
            proof_action.is_dry_run(),
            rng,
            |roots, rng| {
                // Verify the minting proof
                proof.verify(roots, rng)?;

                Ok(())
            },
        )?;

        if proof_action.is_dry_run() {
            // If dry run, just verify and return
            return Ok(());
        }

        // Update asset total supply
        asset_info.total_supply = asset_info
            .total_supply
            .checked_add(amount)
            .ok_or_else(|| anyhow!("Asset supply overflow"))?;

        self.conn.execute(
            "UPDATE assets SET total_supply = ?1 WHERE asset_id = ?2",
            params![asset_info.total_supply, asset_id],
        )?;

        Ok(())
    }

    pub fn get_account_asset_state(
        &self,
        account_info: &DartAccountInfo,
        asset_id: AssetId,
    ) -> Result<AccountAssetState> {
        log::debug!(
            "Getting account asset state for account '{}' and asset '{}'",
            account_info.name,
            asset_id
        );
        let mut stmt = self.conn.prepare(
            "SELECT aas.id, aas.account_db_id, aas.asset_db_id, aas.state_data 
             FROM account_asset_states aas
             JOIN assets a ON aas.asset_db_id = a.id
             WHERE aas.account_db_id = ?1 AND a.asset_id = ?2",
        )?;

        let state_info = stmt.query_row(params![account_info.id, asset_id], |row| {
            Ok(AccountAssetStateInfo {
                id: row.get(0)?,
                account_db_id: row.get(1)?,
                asset_db_id: row.get(2)?,
                state_data: row.get(3)?,
            })
        })?;
        log::debug!(
            "Found account asset state info: {:?} for account '{}' and asset '{}'",
            state_info,
            account_info.name,
            asset_id
        );

        state_info.get_state(account_info)
    }

    fn update_account_asset_state(
        &mut self,
        account_info: &DartAccountInfo,
        state: &AccountAssetState,
    ) -> Result<()> {
        let asset_id = state.asset_id;
        let state_db = AccountAssetStateDb::from_state(state.clone());
        let state_data = state_db.encode();

        self.conn.execute(
            "INSERT OR REPLACE INTO account_asset_states(account_db_id, asset_db_id, state_data) VALUES (?1, (SELECT id FROM assets WHERE asset_id = ?2), ?3)
            ON CONFLICT(account_db_id, asset_db_id) DO UPDATE SET state_data = ?3",
            params![account_info.id, asset_id, state_data],
        )?;

        Ok(())
    }

    // Settlement operations
    pub fn create_settlement_gen_proof<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        venue_id: &str,
        legs: Vec<(String, String, String, String, AssetId, Balance)>, // (sender_signer, sender_account, receiver_signer, receiver_account, asset_id, amount)
    ) -> Result<SettlementProof<()>> {
        let mut leg_builders = Vec::new();

        for (sender_signer, sender_account, receiver_signer, receiver_account, asset_id, amount) in
            legs
        {
            let sender_info = self.get_dart_account(&sender_signer, &sender_account)?;
            let receiver_info = self.get_dart_account(&receiver_signer, &receiver_account)?;
            let asset_info = self.get_asset_by_id(asset_id)?;

            let sender_keys = self.get_account_public_keys(&sender_info)?;
            let receiver_keys = self.get_account_public_keys(&receiver_info)?;
            let auditors = asset_info.auditors()?;
            let mediators = asset_info.mediators()?;
            let asset_state = AssetState::new(asset_id, &auditors, &mediators);

            leg_builders.push(LegBuilder {
                sender: sender_keys,
                receiver: receiver_keys,
                asset: asset_state,
                amount,
            });
        }

        let settlement = SettlementBuilder::new(venue_id.as_bytes());
        let mut builder = settlement;
        for leg in leg_builders {
            builder = builder.leg(leg);
        }
        let settlement = builder.encrypt_and_prove(rng, &self.asset_tree.0)?;

        Ok(settlement)
    }

    // Settlement operations
    pub fn create_settlement_verify_proof<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        settlement: SettlementProof<()>,
    ) -> Result<SettlementId> {
        // Verify settlement proof
        settlement.verify(&self.asset_roots, rng)?;

        // Get next settlement ID
        let settlement_id: SettlementId = self.conn.query_row(
            "SELECT COALESCE(MAX(settlement_id), -1) + 1 FROM settlements",
            [],
            |row| row.get(0),
        )?;

        // Store settlement
        self.conn.execute(
            "INSERT INTO settlements (settlement_id, status) VALUES (?1, 'Pending')",
            params![settlement_id],
        )?;

        let settlement_db_id = self.conn.last_insert_rowid();

        // Store settlement legs
        for (leg_index, leg_proof) in settlement.legs.iter().enumerate() {
            // For encrypted leg, try SCALE encoding first
            let encrypted_leg = leg_proof.leg_enc.encode();
            let has_mediator = leg_proof.has_mediator()?;
            let mediator_status = if has_mediator { Some("Pending") } else { None };

            self.conn.execute(
                "INSERT INTO settlement_legs (settlement_db_id, leg_index, encrypted_leg, sender_status, receiver_status, mediator_status) 
                 VALUES (?1, ?2, ?3, 'Pending', 'Pending', ?4)",
                params![settlement_db_id, leg_index as u32, encrypted_leg, mediator_status],
            )?;
        }

        Ok(settlement_id)
    }

    pub fn sender_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        asset_id: AssetId,
        amount: Balance,
        proof_action: ProofAction,
    ) -> Result<()> {
        log::debug!(
            "Sender affirmation for settlement {}, leg {}",
            settlement_id,
            leg_index
        );
        // Check settlement is in pending state
        let settlement_status = self.get_settlement_status(settlement_id)?;
        let settlement_status = SettlementStatus::from_str(&settlement_status)?;
        if settlement_status != SettlementStatus::Pending {
            return Err(anyhow!("Settlement is not in pending state"));
        }

        // Check sender affirmation status
        let (sender_status, _, _) = self.get_leg_affirmation_statuses(settlement_id, leg_index)?;
        if sender_status != AffirmationStatus::Pending {
            return Err(anyhow!(
                "Sender has already affirmed or settlement leg is not in pending state"
            ));
        }

        self.handle_settlement_state_update_proof(
            rng,
            signer_name,
            account_name,
            settlement_id,
            leg_index,
            LegRole::Sender,
            proof_action,
            |account_keys, leg_ref, leg_enc, leg_enc_rand, leg, account_state, account_tree, rng| {
                if leg.asset_id() != asset_id || leg.amount() != amount {
                    return Err(anyhow!("Leg details don't match provided asset_id/amount"));
                }

                // Generate sender affirmation proof
                Ok(SenderAffirmationProof::new(
                    rng,
                    &account_keys.acct,
                    &leg_ref,
                    amount,
                    leg_enc,
                    leg_enc_rand,
                    account_state,
                    account_tree,
                )?)
            },
            |proof, leg_enc, roots, rng| {
                // Verify the sender affirmation proof
                proof.verify(&leg_enc, roots, rng)?;
                Ok(())
            },
            |conn, settlement_id, leg_index| {
                // Update settlement leg status
                conn.execute(
                    "UPDATE settlement_legs SET sender_status = 'Affirmed' 
                     WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
                    params![settlement_id, leg_index],
                )?;
                Ok(())
            },
        )?;

        Ok(())
    }

    pub fn sender_counter_update<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        proof_action: ProofAction,
    ) -> Result<()> {
        // Check settlement is in executed state
        let settlement_status = self.get_settlement_status(settlement_id)?;
        let settlement_status = SettlementStatus::from_str(&settlement_status)?;
        if settlement_status != SettlementStatus::Executed {
            return Err(anyhow!("Settlement is not in executed state"));
        }

        // Check sender affirmation status
        let (sender_status, _, _) = self.get_leg_affirmation_statuses(settlement_id, leg_index)?;
        if sender_status != AffirmationStatus::Affirmed {
            return Err(anyhow!("Sender has not affirmed this leg"));
        }

        self.handle_settlement_state_update_proof(
            rng,
            signer_name,
            account_name,
            settlement_id,
            leg_index,
            LegRole::Sender,
            proof_action,
            |account_keys, leg_ref, leg_enc, leg_enc_rand, _leg, account_state, account_tree, rng| {
                // Create sender counter update proof
                Ok(SenderCounterUpdateProof::new(
                    rng,
                    &account_keys.acct,
                    &leg_ref,
                    &leg_enc,
                    &leg_enc_rand,
                    account_state,
                    account_tree,
                )?)
            },
            |proof, leg_enc, roots, rng| {
                // Verify the sender counter update proof
                proof.verify(&leg_enc, roots, rng)?;
                Ok(())
            },
            |conn, settlement_id, leg_index| {
                // Update settlement leg status
                conn.execute(
                    "UPDATE settlement_legs SET sender_status = 'Finalized' 
                     WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
                    params![settlement_id, leg_index],
                )?;
                Ok(())
            },
        )?;

        Ok(())
    }

    pub fn sender_reversal<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        proof_action: ProofAction,
    ) -> Result<()> {
        // Check settlement is in rejected state
        let settlement_status = self.get_settlement_status(settlement_id)?;
        let settlement_status = SettlementStatus::from_str(&settlement_status)?;
        if settlement_status != SettlementStatus::Rejected {
            return Err(anyhow!("Settlement is not in rejected state"));
        }

        // Check sender affirmation status
        let (sender_status, _, _) = self.get_leg_affirmation_statuses(settlement_id, leg_index)?;
        if sender_status != AffirmationStatus::Affirmed {
            return Err(anyhow!("Sender has not affirmed this leg"));
        }

        self.handle_settlement_state_update_proof(
            rng,
            signer_name,
            account_name,
            settlement_id,
            leg_index,
            LegRole::Sender,
            proof_action,
            |account_keys, leg_ref, leg_enc, leg_enc_rand, leg, account_state, account_tree, rng| {
                let amount = leg.amount();
                // Create sender reversal proof
                Ok(SenderReversalProof::new(
                    rng,
                    &account_keys.acct,
                    &leg_ref,
                    amount,
                    &leg_enc,
                    &leg_enc_rand,
                    account_state,
                    account_tree,
                )?)
            },
            |proof, leg_enc, roots, rng| {
                // Verify the sender reversal proof
                proof.verify(&leg_enc, roots, rng)?;
                Ok(())
            },
            |conn, settlement_id, leg_index| {
                // Update settlement leg status
                conn.execute(
                    "UPDATE settlement_legs SET sender_status = 'Finalized' 
                     WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
                    params![settlement_id, leg_index],
                )?;
                Ok(())
            },
        )?;

        Ok(())
    }

    pub fn receiver_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        asset_id: AssetId,
        amount: Balance,
        proof_action: ProofAction,
    ) -> Result<()> {
        // Check settlement is in pending state
        let settlement_status = self.get_settlement_status(settlement_id)?;
        let settlement_status = SettlementStatus::from_str(&settlement_status)?;
        if settlement_status != SettlementStatus::Pending {
            return Err(anyhow!("Settlement is not in pending state"));
        }

        // Check receiver affirmation status
        let (_, receiver_status, _) =
            self.get_leg_affirmation_statuses(settlement_id, leg_index)?;
        if receiver_status != AffirmationStatus::Pending {
            return Err(anyhow!(
                "Receiver has already affirmed or settlement leg is not in pending state"
            ));
        }

        self.handle_settlement_state_update_proof(
            rng,
            signer_name,
            account_name,
            settlement_id,
            leg_index,
            LegRole::Receiver,
            proof_action,
            |account_keys, leg_ref, leg_enc, leg_enc_rand, leg, asset_state, account_tree, rng| {
                if leg.asset_id() != asset_id || leg.amount() != amount {
                    return Err(anyhow!("Leg details don't match provided asset_id/amount"));
                }

                // Create receiver affirmation proof
                Ok(ReceiverAffirmationProof::new(
                    rng,
                    &account_keys.acct,
                    &leg_ref,
                    &leg_enc,
                    &leg_enc_rand,
                    asset_state,
                    account_tree,
                )?)
            },
            |proof, leg_enc, roots, rng| {
                // Verify the receiver affirmation proof
                proof.verify(&leg_enc, roots, rng)?;
                Ok(())
            },
            |conn, settlement_id, leg_index| {
                // Update settlement leg status
                conn.execute(
                    "UPDATE settlement_legs SET receiver_status = 'Affirmed' 
                     WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
                    params![settlement_id, leg_index],
                )?;
                Ok(())
            },
        )?;

        Ok(())
    }

    pub fn mediator_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        accept: bool,
        mut proof_action: ProofAction,
    ) -> Result<()> {
        // Check settlement is in pending state
        let settlement_status = self.get_settlement_status(settlement_id)?;
        let settlement_status = SettlementStatus::from_str(&settlement_status)?;
        if settlement_status != SettlementStatus::Pending {
            return Err(anyhow!("Settlement is not in pending state"));
        }

        // Check mediator affirmation status
        let (_, _, mediator_status) =
            self.get_leg_affirmation_statuses(settlement_id, leg_index)?;
        if mediator_status.is_none() {
            return Err(anyhow!("No mediator for this leg"));
        }
        if mediator_status != Some(AffirmationStatus::Pending) {
            return Err(anyhow!(
                "Mediator has already affirmed or rejected this leg"
            ));
        }

        let account_info = self.get_dart_account(signer_name, account_name)?;
        let account_keys = account_info.account_keys()?;

        // Get settlement leg
        let leg_ref = LegRef::new(settlement_id.into(), leg_index as u8);
        let encrypted_leg = self.get_encrypted_leg(settlement_id, leg_index)?;

        let proof = if let Some(proof) = proof_action.get_proof()? {
            proof
        } else {
            // Decrypt leg
            let leg = encrypted_leg.decrypt(LegRole::Mediator(0), &account_keys.enc)?;

            // Create mediator affirmation proof
            MediatorAffirmationProof::new(
                rng,
                &leg_ref,
                leg.asset_id,
                &encrypted_leg,
                &account_keys.enc,
                0,
                accept,
            )?
        };

        // If proof action is to generate only, save proof and return
        if !proof_action.apply_proof() {
            // Save proof to file if requested
            proof_action.save_proof(&proof)?;
            return Ok(());
        }

        // Verify proof
        proof.verify(&encrypted_leg)?;

        if proof_action.is_dry_run() {
            // If dry run, just verify and return
            return Ok(());
        }

        // Update settlement leg status
        let status = if accept { "Affirmed" } else { "Rejected" };
        self.conn.execute(
            "UPDATE settlement_legs SET mediator_status = ?1 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?2) AND leg_index = ?3",
            params![status, settlement_id, leg_index],
        )?;

        self.check_and_update_settlement_status(settlement_id)?;

        Ok(())
    }

    pub fn receiver_claim<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        proof_action: ProofAction,
    ) -> Result<()> {
        // Check settlement is in executed state
        let settlement_status = self.get_settlement_status(settlement_id)?;
        let settlement_status = SettlementStatus::from_str(&settlement_status)?;
        if settlement_status != SettlementStatus::Executed {
            return Err(anyhow!("Settlement is not in executed state"));
        }

        // Check receiver affirmation status
        let (_, receiver_status, _) =
            self.get_leg_affirmation_statuses(settlement_id, leg_index)?;
        if receiver_status != AffirmationStatus::Affirmed {
            return Err(anyhow!("Receiver has not affirmed this leg"));
        }

        self.handle_settlement_state_update_proof(
            rng,
            signer_name,
            account_name,
            settlement_id,
            leg_index,
            LegRole::Receiver,
            proof_action,
            |account_keys, leg_ref, leg_enc, leg_enc_rand, leg, asset_state, account_tree, rng| {
                // Create receiver claim proof
                Ok(ReceiverClaimProof::new(
                    rng,
                    &account_keys.acct,
                    &leg_ref,
                    leg.amount(),
                    &leg_enc,
                    &leg_enc_rand,
                    asset_state,
                    account_tree,
                )?)
            },
            |proof, leg_enc, roots, rng| {
                // Verify the receiver claim proof
                proof.verify(&leg_enc, roots, rng)?;
                Ok(())
            },
            |conn, settlement_id, leg_index| {
                // Update settlement leg status
                conn.execute(
                    "UPDATE settlement_legs SET receiver_status = 'Finalized' 
                     WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
                    params![settlement_id, leg_index],
                )?;
                Ok(())
            },
        )?;

        Ok(())
    }

    fn get_encrypted_leg(
        &self,
        settlement_id: SettlementId,
        leg_index: LegId,
    ) -> Result<LegEncrypted> {
        log::debug!(
            "Getting encrypted leg for settlement {}, leg {}",
            settlement_id,
            leg_index
        );
        let mut stmt = self.conn.prepare(
            "SELECT encrypted_leg FROM settlement_legs 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2"
        )?;

        let encrypted_leg_data: Vec<u8> =
            stmt.query_row(params![settlement_id, leg_index], |row| row.get(0))?;
        log::debug!("Encrypted leg data length: {}", encrypted_leg_data.len());

        let encrypted_leg = Decode::decode(&mut encrypted_leg_data.as_slice())?;
        Ok(encrypted_leg)
    }

    fn check_and_update_settlement_status(&mut self, settlement_id: SettlementId) -> Result<()> {
        // Get all legs for this settlement
        let mut stmt = self.conn.prepare(
            "SELECT sender_status, receiver_status, mediator_status FROM settlement_legs 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1)",
        )?;

        let rows = stmt.query_map(params![settlement_id], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, String>(1)?,
                row.get::<_, Option<String>>(2)?,
            ))
        })?;

        let mut all_affirmed = true;
        let mut any_rejected = false;
        let mut all_finalized = true;

        for row in rows {
            let (sender_status, receiver_status, mediator_status) = row?;

            let sender = AffirmationStatus::from_str(&sender_status)?;
            let receiver = AffirmationStatus::from_str(&receiver_status)?;
            let mediator = mediator_status
                .map(|s| AffirmationStatus::from_str(&s))
                .transpose()?;

            // Calculate the combined leg status using merge logic
            let mut leg_status = sender.merge(receiver)?;
            if let Some(med_status) = mediator {
                leg_status = leg_status.merge(med_status)?;
            }

            match leg_status {
                AffirmationStatus::Pending => {
                    all_affirmed = false;
                    all_finalized = false;
                }
                AffirmationStatus::Rejected => {
                    any_rejected = true;
                    all_affirmed = false;
                }
                AffirmationStatus::Affirmed => {
                    all_finalized = false;
                }
                AffirmationStatus::Finalized => {
                    // This leg is finalized
                }
            }
        }

        let new_status = if any_rejected {
            "Rejected"
        } else if all_finalized {
            "Finalized"
        } else if all_affirmed {
            "Executed"
        } else {
            "Pending"
        };

        self.conn.execute(
            "UPDATE settlements SET status = ?1 WHERE settlement_id = ?2",
            params![new_status, settlement_id],
        )?;

        Ok(())
    }

    // Utility methods
    pub fn list_signers(&self) -> Result<Vec<SignerInfo>> {
        let mut stmt = self
            .conn
            .prepare("SELECT id, name FROM signers ORDER BY name")?;
        let rows = stmt.query_map([], |row| {
            Ok(SignerInfo {
                id: row.get(0)?,
                name: row.get(1)?,
            })
        })?;

        let mut signers = Vec::new();
        for signer in rows {
            signers.push(signer?);
        }
        Ok(signers)
    }

    pub fn list_dart_accounts(
        &self,
        signer_name: Option<&str>,
    ) -> Result<Vec<(String, DartAccountInfo)>> {
        let query = if signer_name.is_some() {
            "SELECT da.id, da.signer_id, da.name, da.account_key, da.encryption_key, da.key_seed, s.name
             FROM dart_accounts da
             JOIN signers s ON da.signer_id = s.id
             WHERE s.name = ?1
             ORDER BY s.name, da.name"
        } else {
            "SELECT da.id, da.signer_id, da.name, da.account_key, da.encryption_key, da.key_seed, s.name
             FROM dart_accounts da
             JOIN signers s ON da.signer_id = s.id
             ORDER BY s.name, da.name"
        };

        let mut stmt = self.conn.prepare(query)?;

        let account_iter = if let Some(signer) = signer_name {
            stmt.query_map(params![signer], Self::map_account_row)?
        } else {
            stmt.query_map([], Self::map_account_row)?
        };

        let mut accounts = Vec::new();
        for account in account_iter {
            accounts.push(account?);
        }
        Ok(accounts)
    }

    fn map_account_row(row: &rusqlite::Row) -> rusqlite::Result<(String, DartAccountInfo)> {
        Ok((
            row.get::<_, String>(6)?, // signer name
            DartAccountInfo {
                id: row.get(0)?,
                signer_id: row.get(1)?,
                name: row.get(2)?,
                account_key: row.get(3)?,
                encryption_key: row.get(4)?,
                key_seed: row.get(5)?,
            },
        ))
    }

    pub fn list_assets(&self) -> Result<Vec<AssetInfo>> {
        let mut stmt = self.conn.prepare(
            "SELECT id, asset_id, issuer_signer_id, auditors, mediators, total_supply FROM assets ORDER BY asset_id"
        )?;
        let rows = stmt.query_map([], |row| {
            Ok(AssetInfo {
                id: row.get(0)?,
                asset_id: row.get(1)?,
                issuer_signer_id: row.get(2)?,
                auditors: row.get(3)?,
                mediators: row.get(4)?,
                total_supply: row.get(5)?,
            })
        })?;

        let mut assets = Vec::new();
        for asset in rows {
            assets.push(asset?);
        }
        Ok(assets)
    }

    pub fn get_settlement_status(&self, settlement_id: SettlementId) -> Result<String> {
        log::debug!("Getting status for settlement ID {}", settlement_id);
        let mut stmt = self
            .conn
            .prepare("SELECT status FROM settlements WHERE settlement_id = ?1")?;
        let status = stmt.query_row(params![settlement_id], |row| row.get::<_, String>(0))?;
        Ok(status)
    }

    fn get_leg_affirmation_statuses(
        &self,
        settlement_id: SettlementId,
        leg_index: LegId,
    ) -> Result<(
        AffirmationStatus,
        AffirmationStatus,
        Option<AffirmationStatus>,
    )> {
        log::debug!(
            "Getting affirmation statuses for settlement ID {}, leg index {}",
            settlement_id,
            leg_index
        );
        let mut stmt = self.conn.prepare(
            "SELECT sender_status, receiver_status, mediator_status FROM settlement_legs 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2"
        )?;

        let (sender_str, receiver_str, mediator_str): (String, String, Option<String>) = stmt
            .query_row(params![settlement_id, leg_index], |row| {
                Ok((row.get(0)?, row.get(1)?, row.get(2)?))
            })?;
        log::debug!(
            "Leg statuses - sender: {}, receiver: {}, mediator: {:?}",
            sender_str,
            receiver_str,
            mediator_str
        );

        let sender_status = AffirmationStatus::from_str(&sender_str)?;
        let receiver_status = AffirmationStatus::from_str(&receiver_str)?;
        let mediator_status = mediator_str
            .map(|s| AffirmationStatus::from_str(&s))
            .transpose()?;

        Ok((sender_status, receiver_status, mediator_status))
    }

    /// Handle account state update proof verification and insertion.
    pub fn handle_account_state_update_proof<R: RngCore + CryptoRng>(
        &mut self,
        account_info: &DartAccountInfo,
        asset_state: &mut AccountAssetState,
        proof: &impl AccountStateUpdate,
        dry_run: bool,
        rng: &mut R,
        verify: impl FnOnce(&AccountRootHistory, &mut R) -> Result<()>,
    ) -> Result<()> {
        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Verify the account state update proof.
        verify(&self.account_roots, rng)?;

        if dry_run {
            // If dry run, just verify and return
            return Ok(());
        }

        // Insert the update account state commitment into the account curve tree.
        let account_commitment = proof.account_state_commitment();
        // Append the account commitment to the account tree
        self.append_account_commitment(account_commitment)?;

        // Add the nullifier to burn the old commitment.
        self.add_nullifier(nullifier)?;

        // Commit the pending state change and save the state.
        asset_state.commit_pending_state()?;
        self.update_account_asset_state(&account_info, &asset_state)?;

        // Append the account commitment to the account tree
        self.append_account_commitment(asset_state.current_state_commitment)?;

        Ok(())
    }

    pub fn handle_settlement_state_update_proof<
        R: RngCore + CryptoRng,
        T: Encode + Decode + AccountStateUpdate,
    >(
        &mut self,
        rng: &mut R,
        signer_name: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        role: LegRole,
        mut proof_action: ProofAction,
        gen_proof: impl FnOnce(
            &AccountKeys,
            LegRef,
            &LegEncrypted,
            &LegEncryptionRandomness,
            &Leg,
            &mut AccountAssetState,
            &AccountCurveTree,
            &mut R,
        ) -> Result<T>,
        verify_proof: impl FnOnce(&T, &LegEncrypted, &AccountRootHistory, &mut R) -> Result<()>,
        update_leg_status: impl FnOnce(&Connection, SettlementId, LegId) -> Result<()>,
    ) -> Result<()> {
        let account_info = self.get_dart_account(signer_name, account_name)?;
        let account_keys = account_info.account_keys()?;

        // Get settlement leg
        let leg_ref = LegRef::new(settlement_id.into(), leg_index as u8);
        let encrypted_leg = self.get_encrypted_leg(settlement_id, leg_index)?;
        let (leg, leg_enc_rand) = encrypted_leg.decrypt_with_randomness(role, &account_keys.enc)?;
        let asset_id = leg.asset_id();

        // Get and update account asset state
        let mut asset_state = self.get_account_asset_state(&account_info, asset_id)?;

        let proof: T = if let Some(proof) = proof_action.get_proof()? {
            proof
        } else {
            // Create sender affirmation proof
            let proof = gen_proof(
                &account_keys,
                leg_ref,
                &encrypted_leg,
                &leg_enc_rand,
                &leg,
                &mut asset_state,
                &self.account_tree,
                rng,
            )?;

            // Update the account state with the pending state change.
            self.update_account_asset_state(&account_info, &asset_state)?;

            proof
        };

        // If proof action is to generate only, save proof and return
        if !proof_action.apply_proof() {
            // Save proof to file if requested
            proof_action.save_proof(&proof)?;
            return Ok(());
        }

        // Verify the proof and handle the account state update.
        self.handle_account_state_update_proof(
            &account_info,
            &mut asset_state,
            &proof,
            proof_action.is_dry_run(),
            rng,
            |roots, rng| {
                // Verify the sender affirmation proof
                verify_proof(&proof, &encrypted_leg, roots, rng)?;

                Ok(())
            },
        )?;

        if proof_action.is_dry_run() {
            // If dry run, just verify and return
            return Ok(());
        }

        // Update settlement leg status
        update_leg_status(&self.conn, settlement_id, leg_index)?;

        self.check_and_update_settlement_status(settlement_id)?;

        Ok(())
    }
}
