use anyhow::{Result, anyhow};
use rusqlite::{Connection, params};
use serde::{Serialize, Deserialize};
use std::path::Path;
use std::sync::Arc;
use rand_core::{RngCore, CryptoRng};
use codec::{Encode, Decode};

use polymesh_dart::*;
use polymesh_dart::curve_tree::CurveTreeRoot;

mod sqlite_curve_tree;
use sqlite_curve_tree::{AssetCurveTree, AccountCurveTree, AssetRootHistory, AccountRootHistory};

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
    pub account_key: Vec<u8>, // SCALE encoded AccountPublicKey
    pub encryption_key: Vec<u8>, // SCALE encoded EncryptionPublicKey
    pub key_seed: String, // Random seed used to generate AccountKeys
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
    pub auditor_or_mediator: Vec<u8>, // Serialized AuditorOrMediator
    pub total_supply: Balance,
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
        let account = account_info.account_keys()?;
        let db_state = AccountAssetStateDb::decode(&mut self.state_data.as_slice())?;
        Ok(AccountAssetState {
            account,
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
    pub pending_state: Option<AccountState>,
}

impl AccountAssetStateDb {
    pub fn from_state(state: AccountAssetState) -> Self {
        Self {
            asset_id: state.asset_id,
            current_state: state.current_state,
            current_state_commitment: state.current_state_commitment,
            current_tx_id: state.current_tx_id,
            pending_state: state.pending_state
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
            "signers"
        ];
        
        for table in &tables {
            self.conn.execute(&format!("DROP TABLE IF EXISTS {}", table), [])?;
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
                auditor_or_mediator BLOB NOT NULL,
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
                root_data BLOB NOT NULL
            )",
            [],
        )?;

        // Account tree roots table
        self.conn.execute(
            "CREATE TABLE IF NOT EXISTS account_root_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
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

        Ok(())
    }

    // Signer operations
    pub fn create_signer(&mut self, name: &str) -> Result<SignerInfo> {
        self.conn.execute(
            "INSERT INTO signers (name) VALUES (?1)",
            params![name],
        )?;

        let id = self.conn.last_insert_rowid();
        Ok(SignerInfo {
            id,
            name: name.to_string(),
        })
    }

    pub fn get_signer_by_name(&self, name: &str) -> Result<SignerInfo> {
        let mut stmt = self.conn.prepare("SELECT id, name FROM signers WHERE name = ?1")?;
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
        account_name: &str
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
            params![signer.id, account_name, account_key_bytes, encryption_key_bytes, key_seed],
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

    pub fn get_dart_account(&self, signer_name: &str, account_name: &str) -> Result<DartAccountInfo> {
        let mut stmt = self.conn.prepare(
            "SELECT da.id, da.signer_id, da.name, da.account_key, da.encryption_key, da.key_seed
             FROM dart_accounts da
             JOIN signers s ON da.signer_id = s.id
             WHERE s.name = ?1 AND da.name = ?2"
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

    pub fn get_account_public_keys(&self, account_info: &DartAccountInfo) -> Result<AccountPublicKeys> {
        let acct = AccountPublicKey::decode(&mut account_info.account_key.as_slice())?;
        let enc = EncryptionPublicKey::decode(&mut account_info.encryption_key.as_slice())?;
        Ok(AccountPublicKeys { acct, enc })
    }

    // Asset operations
    pub fn create_asset(&mut self, issuer_signer_name: &str, auditor: AuditorOrMediator) -> Result<AssetInfo> {
        let signer = self.get_signer_by_name(issuer_signer_name)?;
        
        // Get next asset ID
        let asset_id: AssetId = self.conn.query_row(
            "SELECT COALESCE(MAX(asset_id), -1) + 1 FROM assets",
            [],
            |row| row.get(0)
        )?;

        let auditor_bytes = auditor.encode();

        self.conn.execute(
            "INSERT INTO assets (asset_id, issuer_signer_id, auditor_or_mediator, total_supply) 
             VALUES (?1, ?2, ?3, 0)",
            params![asset_id, signer.id, auditor_bytes],
        )?;

        let id = self.conn.last_insert_rowid();
        
        // Update the asset tree
        let asset_state = self.create_asset_state(asset_id, &auditor)?;
        let leaf_index = asset_id as _;
        self.asset_tree.update_leaf(leaf_index, asset_state.commitment()?.as_leaf_value()?)?;

        Ok(AssetInfo {
            id,
            asset_id,
            issuer_signer_id: signer.id,
            auditor_or_mediator: auditor_bytes,
            total_supply: 0,
        })
    }

    fn create_asset_state(&self, asset_id: AssetId, auditor: &AuditorOrMediator) -> Result<AssetState> {
        let (is_mediator, pk) = match auditor {
            AuditorOrMediator::Auditor(pk) => (false, pk.clone()),
            AuditorOrMediator::Mediator(pk) => (true, pk.acct.into()),
        };
        Ok(AssetState::new(asset_id, is_mediator, pk))
    }

    pub fn get_asset_by_id(&self, asset_id: AssetId) -> Result<AssetInfo> {
        let mut stmt = self.conn.prepare(
            "SELECT id, asset_id, issuer_signer_id, auditor_or_mediator, total_supply FROM assets WHERE asset_id = ?1"
        )?;
        
        let asset = stmt.query_row(params![asset_id], |row| {
            Ok(AssetInfo {
                id: row.get(0)?,
                asset_id: row.get(1)?,
                issuer_signer_id: row.get(2)?,
                auditor_or_mediator: row.get(3)?,
                total_supply: row.get(4)?,
            })
        })?;
        Ok(asset)
    }

    // End block operation
    pub fn end_block(&mut self) -> Result<()> {
        // Process all pending account commitments
        let mut stmt = self.conn.prepare(
            "SELECT commitment_data FROM pending_account_commitments ORDER BY id"
        )?;
        
        let commitment_rows = stmt.query_map([], |row| {
            Ok(row.get::<_, Vec<u8>>(0)?)
        })?;
        
        // Insert all pending commitments into account tree
        for commitment_data in commitment_rows {
            let commitment_data = commitment_data?;
            let commitment = AccountStateCommitment::decode(&mut commitment_data.as_slice())?;
            self.account_tree.insert_leaf(commitment.as_leaf_value()?)?;
        }
        
        // Clear pending commitments
        self.conn.execute("DELETE FROM pending_account_commitments", [])?;
        
        // Get current tree roots
        let asset_root = CurveTreeRoot::new(&self.asset_tree.root_node()?)?;
        let account_root = CurveTreeRoot::new(&self.account_tree.root_node()?)?;
        
        // Store roots in database
        self.asset_roots.add_root(&asset_root)?;
        self.account_roots.add_root(&account_root)?;
        
        Ok(())
    }

    fn append_account_commitment(
        &mut self, 
        commitment: AccountStateCommitment
    ) -> Result<()> {
        // Store commitment in pending table instead of directly inserting into tree
        let commitment_data = commitment.encode();
        self.conn.execute(
            "INSERT INTO pending_account_commitments (commitment_data) VALUES (?1)",
            params![commitment_data],
        )?;
        
        Ok(())
    }

    // Asset registration operations
    pub fn register_account_with_asset<R: RngCore + CryptoRng>(
        &mut self, 
        rng: &mut R,
        signer_name: &str, 
        account_name: &str, 
        asset_id: AssetId
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
            return Err(anyhow!("Account {} is already registered with asset {}", account_name, asset_id));
        }
        
        // Create registration proof and initial state
        let account_keys = account_info.account_keys()?;
        let (proof, mut asset_state) = AccountAssetRegistrationProof::new(
            rng, 
            &account_keys, 
            asset_id, 
            signer_name.as_bytes()
        )?;
        
        // Verify the proof
        proof.verify(signer_name.as_bytes())?;
        
        // Register in database
        self.conn.execute(
            "INSERT INTO asset_registered_accounts (account_db_id, asset_db_id) VALUES (?1, ?2)",
            params![account_info.id, asset_info.id],
        )?;
        
        // Store the account asset state
        asset_state.commit_pending_state()?;
        self.update_account_asset_state(&account_info, asset_id, &asset_state)?;

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
    ) -> Result<()> {
        let account_info = self.get_dart_account(issuer_signer_name, account_name)?;
        let mut asset_info = self.get_asset_by_id(asset_id)?;
        
        // Verify issuer owns the asset
        if asset_info.issuer_signer_id != account_info.signer_id {
            return Err(anyhow!("Signer {} is not the issuer of asset {}", issuer_signer_name, asset_id));
        }
        
        // Get and update account asset state
        let mut asset_state = self.get_account_asset_state(&account_info, asset_id)?;
        
        // Create minting proof
        let proof = AssetMintingProof::new(rng, &mut asset_state, &self.account_tree, amount)?;
        
        // Verify proof
        proof.verify(&self.account_roots, rng)?;
        
        // Update asset total supply
        asset_info.total_supply = asset_info.total_supply.checked_add(amount)
            .ok_or_else(|| anyhow!("Asset supply overflow"))?;
        
        self.conn.execute(
            "UPDATE assets SET total_supply = ?1 WHERE asset_id = ?2",
            params![asset_info.total_supply, asset_id],
        )?;
        
        // Update account asset state
        asset_state.commit_pending_state()?;
        self.update_account_asset_state(&account_info, asset_id, &asset_state)?;

        // Append the account commitment to the account tree
        self.append_account_commitment(asset_state.current_state_commitment)?;
        
        Ok(())
    }

    pub fn get_account_asset_state(&self, account_info: &DartAccountInfo, asset_id: AssetId) -> Result<AccountAssetState> {
        let mut stmt = self.conn.prepare(
            "SELECT aas.id, aas.account_db_id, aas.asset_db_id, aas.state_data 
             FROM account_asset_states aas
             JOIN assets a ON aas.asset_db_id = a.id
             WHERE aas.account_db_id = ?1 AND a.asset_id = ?2"
        )?;
        
        let state_info = stmt.query_row(params![account_info.id, asset_id], |row| {
            Ok(AccountAssetStateInfo {
                id: row.get(0)?,
                account_db_id: row.get(1)?,
                asset_db_id: row.get(2)?,
                state_data: row.get(3)?,
            })
        })?;
        
        state_info.get_state(account_info)
    }

    fn update_account_asset_state(&mut self, account_info: &DartAccountInfo, asset_id: AssetId, state: &AccountAssetState) -> Result<()> {
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
    pub fn create_settlement<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        venue_id: &str,
        legs: Vec<(String, String, String, String, AssetId, Balance)>, // (sender_signer, sender_account, receiver_signer, receiver_account, asset_id, amount)
    ) -> Result<SettlementId> {
        let mut leg_builders = Vec::new();
        
        for (sender_signer, sender_account, receiver_signer, receiver_account, asset_id, amount) in legs {
            let sender_info = self.get_dart_account(&sender_signer, &sender_account)?;
            let receiver_info = self.get_dart_account(&receiver_signer, &receiver_account)?;
            let asset_info = self.get_asset_by_id(asset_id)?;
            
            let sender_keys = self.get_account_public_keys(&sender_info)?;
            let receiver_keys = self.get_account_public_keys(&receiver_info)?;
            let auditor = AuditorOrMediator::decode(&mut asset_info.auditor_or_mediator.as_slice())?;
            
            leg_builders.push(LegBuilder {
                sender: sender_keys,
                receiver: receiver_keys,
                asset_id,
                amount,
                mediator: auditor,
            });
        }
        
        let settlement = SettlementBuilder::<()>::new(venue_id.as_bytes());
        let mut builder = settlement;
        for leg in leg_builders {
            builder = builder.leg(leg);
        }
        let settlement = builder.encryt_and_prove(rng, &self.asset_tree.0)?;
        
        // Verify settlement proof
        settlement.verify(&self.asset_roots, rng)?;
        
        // Get next settlement ID
        let settlement_id: SettlementId = self.conn.query_row(
            "SELECT COALESCE(MAX(settlement_id), -1) + 1 FROM settlements",
            [],
            |row| row.get(0)
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
            let encrypted_leg = leg_proof.leg_enc()?.encode();
            let has_mediator = leg_proof.has_mediator()?;
            
            self.conn.execute(
                "INSERT INTO settlement_legs (settlement_db_id, leg_index, encrypted_leg, sender_status, receiver_status, mediator_status) 
                 VALUES (?1, ?2, ?3, 'Pending', 'Pending', ?4)",
                params![settlement_db_id, leg_index as u32, encrypted_leg, 
                       if has_mediator { Some("Pending") } else { None }],
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
    ) -> Result<()> {
        let account_info = self.get_dart_account(signer_name, account_name)?;
        let account_keys = account_info.account_keys()?;
        
        // Get settlement leg
        let leg_ref = LegRef::new(settlement_id.into(), leg_index as u8);
        let encrypted_leg = self.get_encrypted_leg(settlement_id, leg_index)?;
        
        // Decrypt leg and verify sender
        let sk_e = encrypted_leg.decrypt_sk_e(LegRole::Sender, &account_keys.enc)?;
        let leg = encrypted_leg.decrypt(LegRole::Sender, &account_keys.enc)?;
        
        if leg.asset_id() != asset_id || leg.amount() != amount {
            return Err(anyhow!("Leg details don't match provided asset_id/amount"));
        }
        
        // Get and update account asset state
        let mut asset_state = self.get_account_asset_state(&account_info, asset_id)?;
        
        // Create sender affirmation proof
        let proof = SenderAffirmationProof::new(
            rng,
            &leg_ref,
            amount,
            sk_e,
            &encrypted_leg,
            &mut asset_state,
            &self.account_tree,
        )?;
        
        // Verify proof
        proof.verify(&encrypted_leg, &self.account_roots, rng)?;
        
        // Update settlement leg status
        self.conn.execute(
            "UPDATE settlement_legs SET sender_status = 'Affirmed' 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
            params![settlement_id, leg_index],
        )?;
        
        // Update account asset state
        asset_state.commit_pending_state()?;
        self.update_account_asset_state(&account_info, asset_id, &asset_state)?;

        // Append the account commitment to the account tree
        self.append_account_commitment(asset_state.current_state_commitment)?;
        
        self.check_and_update_settlement_status(settlement_id)?;
        
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
    ) -> Result<()> {
        let account_info = self.get_dart_account(signer_name, account_name)?;
        let account_keys = account_info.account_keys()?;
        
        // Get settlement leg
        let leg_ref = LegRef::new(settlement_id.into(), leg_index as u8);
        let encrypted_leg = self.get_encrypted_leg(settlement_id, leg_index)?;
        
        // Decrypt leg and verify receiver
        let sk_e = encrypted_leg.decrypt_sk_e(LegRole::Receiver, &account_keys.enc)?;
        let leg = encrypted_leg.decrypt(LegRole::Receiver, &account_keys.enc)?;
        
        if leg.asset_id() != asset_id || leg.amount() != amount {
            return Err(anyhow!("Leg details don't match provided asset_id/amount"));
        }
        
        // Get and update account asset state
        let mut asset_state = self.get_account_asset_state(&account_info, asset_id)?;
        
        // Create receiver affirmation proof
        let proof = ReceiverAffirmationProof::new(
            rng,
            &leg_ref,
            sk_e,
            &encrypted_leg,
            &mut asset_state,
            &self.account_tree,
        )?;
        
        // Verify proof
        proof.verify(&encrypted_leg, &self.account_roots, rng)?;
        
        // Update settlement leg status
        self.conn.execute(
            "UPDATE settlement_legs SET receiver_status = 'Affirmed' 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
            params![settlement_id, leg_index],
        )?;
        
        // Update account asset state
        asset_state.commit_pending_state()?;
        self.update_account_asset_state(&account_info, asset_id, &asset_state)?;

        // Append the account commitment to the account tree
        self.append_account_commitment(asset_state.current_state_commitment)?;
        
        self.check_and_update_settlement_status(settlement_id)?;
        
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
    ) -> Result<()> {
        let account_info = self.get_dart_account(signer_name, account_name)?;
        let account_keys = account_info.account_keys()?;
        
        // Get settlement leg
        let leg_ref = LegRef::new(settlement_id.into(), leg_index as u8);
        let encrypted_leg = self.get_encrypted_leg(settlement_id, leg_index)?;
        
        // Decrypt leg
        let sk_e = encrypted_leg.decrypt_sk_e(LegRole::Mediator, &account_keys.enc)?;
        let _leg = encrypted_leg.decrypt(LegRole::Mediator, &account_keys.enc)?;
        
        // Create mediator affirmation proof
        let proof = MediatorAffirmationProof::new(
            rng,
            &leg_ref,
            sk_e,
            &encrypted_leg,
            &account_keys.acct,
            accept,
        )?;
        
        // Verify proof
        proof.verify(&encrypted_leg)?;
        
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
    ) -> Result<()> {
        let account_info = self.get_dart_account(signer_name, account_name)?;
        let account_keys = account_info.account_keys()?;
        
        // Get settlement leg
        let leg_ref = LegRef::new(settlement_id.into(), leg_index as u8);
        let encrypted_leg = self.get_encrypted_leg(settlement_id, leg_index)?;
        
        // Decrypt leg
        let sk_e = encrypted_leg.decrypt_sk_e(LegRole::Receiver, &account_keys.enc)?;
        let leg = encrypted_leg.decrypt(LegRole::Receiver, &account_keys.enc)?;
        let asset_id = leg.asset_id();
        let amount = leg.amount();
        
        // Get and update account asset state
        let mut asset_state = self.get_account_asset_state(&account_info, asset_id)?;
        
        // Create receiver claim proof
        let proof = ReceiverClaimProof::new(
            rng,
            &leg_ref,
            amount,
            sk_e,
            &encrypted_leg,
            &mut asset_state,
            &self.account_tree,
        )?;
        
        // Verify proof
        proof.verify(&encrypted_leg, &self.account_roots, rng)?;
        
        // Update settlement leg status
        self.conn.execute(
            "UPDATE settlement_legs SET receiver_status = 'Finalized' 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2",
            params![settlement_id, leg_index],
        )?;
        
        // Update account asset state
        asset_state.commit_pending_state()?;
        self.update_account_asset_state(&account_info, asset_id, &asset_state)?;

        // Append the account commitment to the account tree
        self.append_account_commitment(asset_state.current_state_commitment)?;
        
        self.check_and_update_settlement_status(settlement_id)?;
        
        Ok(())
    }

    fn get_encrypted_leg(&self, settlement_id: SettlementId, leg_index: LegId) -> Result<LegEncrypted> {
        let mut stmt = self.conn.prepare(
            "SELECT encrypted_leg FROM settlement_legs 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1) AND leg_index = ?2"
        )?;
        
        let encrypted_leg_data: Vec<u8> = stmt.query_row(params![settlement_id, leg_index], |row| {
            row.get(0)
        })?;
        
        let encrypted_leg = LegEncrypted::decode(&mut encrypted_leg_data.as_slice())?;
        Ok(encrypted_leg)
    }

    fn check_and_update_settlement_status(&mut self, settlement_id: SettlementId) -> Result<()> {
        // Get all legs for this settlement
        let mut stmt = self.conn.prepare(
            "SELECT sender_status, receiver_status, mediator_status FROM settlement_legs 
             WHERE settlement_db_id = (SELECT id FROM settlements WHERE settlement_id = ?1)"
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
            
            if sender_status != "Affirmed" && sender_status != "Finalized" {
                all_affirmed = false;
                all_finalized = false;
            }
            if receiver_status != "Affirmed" && receiver_status != "Finalized" {
                all_affirmed = false;
                all_finalized = false;
            }
            if let Some(med_status) = mediator_status {
                if med_status == "Rejected" {
                    any_rejected = true;
                }
                if med_status != "Affirmed" && med_status != "Finalized" {
                    all_affirmed = false;
                    all_finalized = false;
                }
            }
            
            if sender_status != "Finalized" || receiver_status != "Finalized" {
                all_finalized = false;
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
        let mut stmt = self.conn.prepare("SELECT id, name FROM signers ORDER BY name")?;
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

    pub fn list_dart_accounts(&self, signer_name: Option<&str>) -> Result<Vec<(String, DartAccountInfo)>> {
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
            }
        ))
    }

    pub fn list_assets(&self) -> Result<Vec<AssetInfo>> {
        let mut stmt = self.conn.prepare(
            "SELECT id, asset_id, issuer_signer_id, auditor_or_mediator, total_supply FROM assets ORDER BY asset_id"
        )?;
        let rows = stmt.query_map([], |row| {
            Ok(AssetInfo {
                id: row.get(0)?,
                asset_id: row.get(1)?,
                issuer_signer_id: row.get(2)?,
                auditor_or_mediator: row.get(3)?,
                total_supply: row.get(4)?,
            })
        })?;
        
        let mut assets = Vec::new();
        for asset in rows {
            assets.push(asset?);
        }
        Ok(assets)
    }

    pub fn get_settlement_status(&self, settlement_id: SettlementId) -> Result<String> {
        let mut stmt = self.conn.prepare("SELECT status FROM settlements WHERE settlement_id = ?1")?;
        let status = stmt.query_row(params![settlement_id], |row| {
            row.get::<_, String>(0)
        })?;
        Ok(status)
    }
}
