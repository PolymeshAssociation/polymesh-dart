//! A CLI that simulates the Confidential Assets pallet off-chain.
//!
//! The CLI plays both sides of a DART deployment:
//! - the **prover** (client) side: account keys, decrypted legs, `AccountAssetState` bookkeeping,
//!   and proof generation/serialization (`-w`);
//! - the **chain** side: pallet storage in SQLite (`storage.rs`), the curve-tree backends and
//!   block hooks (`curve_tree.rs`), the settlement state machine (`settlement.rs`), pallet-mirrored
//!   limits (`config.rs`), pallet `Error<T>` names (`errors.rs`), and a dispatch/event trace
//!   (`trace.rs`).
//!
//! Every simulated extrinsic runs inside a SQLite transaction mirroring the pallet's storage
//! transaction: checks run first, then proof verification, then state application; any failure
//! rolls the whole extrinsic back (see `Chain::dispatch`). On the prover side, proof generation
//! is off-chain work: it touches only the prover's own state and never mutates chain storage.
//!
//! Proof types are parameterized with `PolymeshLimits` and decoded with `DecodeWithMemTracking`,
//! so proof bytes and container bounds match what the pallet accepts.

use std::cell::RefCell;
use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use bounded_collections::BoundedVec;
use codec::{Decode, DecodeWithMemTracking, Encode};
use rand_core::{CryptoRng, RngCore};
use rusqlite::{params, OptionalExtension};

use polymesh_dart::curve_tree::{
    get_account_curve_tree_parameters, AccountTreeConfig, AssetTreeConfig, CompressedCurveTreeRoot,
    CompressedLeafValue, FeeAccountTreeConfig,
};
use polymesh_dart::key_distribution_proof::KeyDistributionProof;
use polymesh_dart::*;

pub mod config;
pub mod corpus;
pub mod curve_tree;
pub mod errors;
pub mod settlement;
pub mod storage;
pub mod trace;

pub use config::{Moment, TestConfig, TreeKind};
pub use corpus::encode_hex;
pub use curve_tree::{AccountTree, AssetTree, ChainTree, FeeAccountTree};
pub use errors::{ChainError, ChainFailure, ChainResult, PALLET_ERROR_NAMES};
pub use polymesh_dart::{
    AssetId, AssetKeysLookup, AssetPkTLookup, AssetState, Balance, BatchedProof, BatchedProofs,
    BlockNumber, EncryptionPublicKey, FeePaymentWithBatchedProofs, Leg, LegBuilder, LegConfig,
    LegEncrypted, LegId, LegRef, LegRole, MediatorId, NodeLevel, PartyVisibility,
    SettlementBuilder, SettlementProof, SettlementRef,
};
pub use settlement::{
    AffirmationStatus, LegAffirmParty, PendingCounts, Settlement, SettlementStatus,
};
pub use storage::{signer_to_did, AccountRow, AssetDetails, Store};
pub use trace::Trace;

use corpus::{CorpusHeader, RecordedOp, Recorder, CORPUS_FORMAT, CORPUS_VERSION};

/// The limits the pallet uses in its extrinsic signatures. The CLI generates and verifies with
/// the same type so proof bytes are byte-comparable with on-chain submissions (GAPS.md §6).
pub type Limits = PolymeshLimits;

/// The action to take with the proof of an extrinsic.
///
/// `-w <path>` generates and writes a proof without applying it (the CLI acts as the client);
/// `-r <path>` reads a proof, verifies it, and applies it (the CLI acts as the chain).
#[derive(Debug)]
pub enum ProofAction {
    GenerateOnly(File),
    ApplyOnly { proof: Vec<u8>, dry_run: bool },
    GenerateAndApply { dry_run: bool },
}

impl ProofAction {
    pub fn new(write: Option<PathBuf>, read: Option<PathBuf>, dry_run: bool) -> ChainResult<Self> {
        match (write, read) {
            (Some(write_path), None) => {
                let file = File::create(&write_path).map_err(|e| {
                    ChainFailure::Internal(format!("cannot create {}: {e}", write_path.display()))
                })?;
                Ok(ProofAction::GenerateOnly(file))
            }
            (None, Some(read_path)) => {
                let proof = std::fs::read(&read_path).map_err(|e| {
                    ChainFailure::Internal(format!("cannot read {}: {e}", read_path.display()))
                })?;
                Ok(ProofAction::ApplyOnly { proof, dry_run })
            }
            (Some(_), Some(_)) => Err(ChainFailure::Internal(
                "cannot specify both write and read paths".into(),
            )),
            (None, None) => Ok(ProofAction::GenerateAndApply { dry_run }),
        }
    }

    /// Decode a proof provided with `-r`. Uses `DecodeWithMemTracking`, the same bound the
    /// pallet requires for extrinsic parameters (bounded-container/memory tracking, GAPS.md §6).
    pub fn get_proof<T: DecodeWithMemTracking>(&self) -> ChainResult<Option<T>> {
        match self {
            ProofAction::GenerateOnly(_) => Ok(None),
            ProofAction::ApplyOnly { proof, .. } => decode_exact::<T>(proof, "proof").map(Some),
            ProofAction::GenerateAndApply { .. } => Ok(None),
        }
    }

    pub fn save_proof<T: Encode>(&mut self, proof: &T) -> ChainResult<()> {
        match self {
            ProofAction::GenerateOnly(file) => {
                file.write_all(&proof.encode())
                    .map_err(ChainFailure::from)?;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    pub fn apply_proof(&self) -> bool {
        !matches!(self, ProofAction::GenerateOnly(_))
    }

    pub fn is_dry_run(&self) -> bool {
        matches!(
            self,
            ProofAction::ApplyOnly { dry_run: true, .. }
                | ProofAction::GenerateAndApply { dry_run: true }
        )
    }
}

/// The simulated chain: pallet storage plus the three curve trees.
pub struct Chain {
    pub store: Arc<Store>,
    pub asset_tree: ChainTree<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>,
    pub account_tree: ChainTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    pub fee_tree: ChainTree<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>,
    /// Optional corpus recorder (`--record`); append-only, never set during replay.
    recorder: RefCell<Option<Recorder>>,
}

impl Chain {
    pub fn open<P: AsRef<Path>>(path: P, config: TestConfig) -> ChainResult<Self> {
        let store = Arc::new(Store::connect(path, config)?);
        let asset_tree = ChainTree::new(store.clone(), TreeKind::Asset)?;
        let account_tree = ChainTree::new(store.clone(), TreeKind::Account)?;
        let fee_tree = ChainTree::new(store.clone(), TreeKind::FeeAccount)?;
        Ok(Self {
            store,
            asset_tree,
            account_tree,
            fee_tree,
            recorder: RefCell::new(None),
        })
    }

    /// Attach a corpus recorder (`--record FILE`). The file is created with a header from the
    /// chain's seed/config, or validated against the existing header and appended to.
    pub fn attach_recorder(&self, path: &Path) -> ChainResult<()> {
        self.attach_recorder_with(path, false)
    }

    /// Start a new recording session (used by `init`): refuse an existing corpus so two runs
    /// cannot be mixed into one file.
    pub fn attach_recorder_new(&self, path: &Path) -> ChainResult<()> {
        self.attach_recorder_with(path, true)
    }

    fn attach_recorder_with(&self, path: &Path, start_new: bool) -> ChainResult<()> {
        let seed = self
            .store
            .run_seed()?
            .ok_or_else(|| ChainFailure::Internal("run `init` before recording a corpus".into()))?;
        let header = CorpusHeader {
            format: CORPUS_FORMAT.to_string(),
            version: CORPUS_VERSION,
            seed,
            config: self.store.config.clone(),
            tool_version: env!("CARGO_PKG_VERSION").to_string(),
        };
        let recorder = Recorder::open(path, &header, start_new)?;
        *self.recorder.borrow_mut() = Some(recorder);
        Ok(())
    }

    /// Record an applied transaction with its outcome (`Ok` or a pallet error name).
    fn record_result<T>(&self, op: RecordedOp, result: &ChainResult<T>) {
        let mut slot = self.recorder.borrow_mut();
        let Some(recorder) = slot.as_mut() else {
            return;
        };
        let (outcome, detail) = match result {
            Ok(_) => ("Ok".to_string(), None),
            Err(e) => (e.name().to_string(), Some(format!("{e}"))),
        };
        let block = self.store.block_number().unwrap_or(0);
        if let Err(e) = recorder.record(block, op, outcome, detail) {
            log::error!("failed to append to the corpus: {e}");
        }
    }

    /// Record a successful setup operation (create signer/account/asset, end-block, ...).
    fn record_ok(&self, op: RecordedOp) {
        let ok: ChainResult<()> = Ok(());
        self.record_result(op, &ok);
    }

    pub fn initialize(&self) -> ChainResult<()> {
        self.store.initialize()?;
        // Genesis roots for the current (block 1) tree states, mirroring the pallet's
        // `get_*_curve_tree()` at genesis.
        self.asset_tree.clone().tree.init_root()?;
        self.account_tree.clone().tree.init_root()?;
        self.fee_tree.clone().tree.init_root()?;
        Ok(())
    }

    // ---------------------------------------------------------------- dispatch framework

    /// Run one simulated extrinsic as the pallet would: checks, verify, apply — inside a
    /// storage transaction that rolls back on any failure (GAPS.md §6, item P0-5).
    ///
    /// `dry_run` runs the full body and then rolls back, so `--dry-run` verifies without
    /// applying state.
    pub fn dispatch<R>(
        &self,
        call: &str,
        dry_run: bool,
        f: impl FnOnce(&Self) -> ChainResult<R>,
    ) -> ChainResult<R> {
        self.store.begin_tx()?;
        match f(self) {
            Ok(v) => {
                if dry_run {
                    self.store.rollback_tx()?;
                    if let Err(trace_err) = self.store.flush_trace(call, Some("DryRun"), Vec::new())
                    {
                        log::error!("failed to record trace for {call}: {trace_err}");
                    }
                } else {
                    self.store.commit_tx()?;
                    if let Err(trace_err) = self.store.flush_trace(call, None, Vec::new()) {
                        log::error!("failed to record trace for {call}: {trace_err}");
                    }
                }
                Ok(v)
            }
            Err(e) => {
                self.store.rollback_tx()?;
                let diagnostics = vec![format!("{e}")];
                if let Err(trace_err) = self.store.flush_trace(call, Some(e.name()), diagnostics) {
                    log::error!("failed to record trace for {call}: {trace_err}");
                }
                Err(e)
            }
        }
    }

    // ---------------------------------------------------------------- identities & accounts (prover side)

    pub fn create_signer(&self, name: &str) -> ChainResult<i64> {
        let result = self.store.create_identity(name);
        if result.is_ok() {
            self.record_ok(RecordedOp::CreateSigner {
                name: name.to_string(),
            });
        }
        result
    }

    pub fn did_for_signer(&self, signer: &str) -> ChainResult<[u8; 32]> {
        let id = self.store.identity_id(signer)?;
        self.store.did_for_identity(id)
    }

    /// Create a confidential account for a signer. This is prover-side bookkeeping: the keys are
    /// generated locally and registered on-chain by `register_accounts`.
    pub fn create_account<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
    ) -> ChainResult<AccountRow> {
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed);
        let key_seed = hex::encode(seed);
        let keys = AccountKeys::from_seed(&key_seed).map_err(ChainFailure::from)?;
        self.create_account_with_keys(signer, account_name, &key_seed, &keys.public_keys())
    }

    /// Create a confidential account from an existing key seed / public keys. Used by `replay`
    /// (the recorded public keys are the chain's account state; no secret is required to apply
    /// proofs) and by [`Self::create_account`] after generating the key material.
    pub fn create_account_with_keys(
        &self,
        signer: &str,
        account_name: &str,
        key_seed: &str,
        public_keys: &AccountPublicKeys,
    ) -> ChainResult<AccountRow> {
        let identity_id = self.store.identity_id(signer)?;
        self.store
            .create_account(identity_id, account_name, key_seed, public_keys)?;
        let account = self
            .store
            .account(signer, account_name)?
            .ok_or_else(|| ChainFailure::Internal("account creation failed".into()))?;
        self.record_ok(RecordedOp::CreateAccount {
            signer: signer.to_string(),
            account: account_name.to_string(),
            key_seed: account.key_seed.clone(),
            public_keys: crate::corpus::encode_hex(&account.public_keys),
        });
        Ok(account)
    }

    pub fn find_account(&self, signer: &str, account: &str) -> ChainResult<AccountRow> {
        self.store
            .account(signer, account)?
            .ok_or_else(|| ChainFailure::Internal(format!("no account '{signer}:{account}'")))
    }

    /// Find the account of `signer` that is registered with `asset_id`. When several of the
    /// signer's accounts are registered, the request is ambiguous (GAPS.md §7).
    pub fn find_account_by_asset(
        &self,
        signer: &str,
        asset_id: AssetId,
    ) -> ChainResult<AccountRow> {
        let mut found: Option<AccountRow> = None;
        let mut stmt = self.store.conn.prepare(
            "SELECT a.id FROM accounts a JOIN identities i ON a.identity_id = i.id WHERE i.name = ?1 ORDER BY a.id",
        )?;
        let mut ids = stmt.query_map(params![signer], |row| row.get::<_, i64>(0))?;
        while let Some(id) = ids.next().transpose()? {
            let account = self
                .store
                .account_by_rowid(id)?
                .ok_or_else(|| ChainFailure::Internal("missing account row".into()))?;
            if self
                .store
                .account_asset_registered(&account.public_keys.acct, asset_id)?
            {
                if found.is_some() {
                    return Err(ChainFailure::Internal(format!(
                        "signer '{signer}' has multiple accounts registered with asset {asset_id}; name the account"
                    )));
                }
                found = Some(account);
            }
        }
        found.ok_or_else(|| {
            ChainFailure::Internal(format!(
                "no account of signer '{signer}' is registered with asset {asset_id}"
            ))
        })
    }

    // ---------------------------------------------------------------- shared chain checks

    /// `ensure_dart_account_registered`: `AccountDid::get`.
    fn ensure_account_registered(&self, account: &AccountPublicKey) -> ChainResult<i64> {
        self.store
            .account_did(account)?
            .ok_or(ChainFailure::Error(ChainError::AccountMissing))
    }

    /// `ensure_dart_account_and_encryption_key_registered`.
    fn ensure_account_and_enc_key_registered(
        &self,
        account: &AccountPublicKey,
        encryption: &EncryptionPublicKey,
    ) -> ChainResult<i64> {
        let did = self.ensure_account_registered(account)?;
        let account_enc = self
            .store
            .account_encryption_key(account)?
            .ok_or(ChainFailure::Error(ChainError::EncryptionKeyMissing))?;
        if account_enc != *encryption {
            // A mediator's key may also be a shared key distributed to the account key
            // (`SharedKeyRecipients`); P1 wires that path.
            return Err(ChainFailure::Error(ChainError::EncryptionKeyMismatch));
        }
        Ok(did)
    }

    /// `ensure_dart_asset_exists`: `Details::get`.
    fn ensure_asset_exists(&self, asset_id: AssetId) -> ChainResult<AssetDetails> {
        self.store
            .asset_details(asset_id)?
            .ok_or(ChainFailure::Error(ChainError::AssetMissing))
    }

    /// `ensure_dart_asset_owner`.
    fn ensure_asset_owner(
        &self,
        caller_identity_id: i64,
        asset_id: AssetId,
    ) -> ChainResult<AssetDetails> {
        let details = self.ensure_asset_exists(asset_id)?;
        if details.issuer_identity_id != caller_identity_id {
            return Err(ChainFailure::Error(ChainError::NotAssetOwner));
        }
        Ok(details)
    }

    /// `ensure_dart_account_permissions`: caller must own the proof's account.
    fn ensure_account_permissions(
        &self,
        caller_identity_id: i64,
        account: &AccountPublicKey,
        encryption: &EncryptionPublicKey,
    ) -> ChainResult<()> {
        let account_did = self.ensure_account_and_enc_key_registered(account, encryption)?;
        if account_did != caller_identity_id {
            return Err(ChainFailure::Error(ChainError::NotAccountOwner));
        }
        Ok(())
    }

    /// `ensure_encryption_key_registered`: `EncryptionKeyDid::get`.
    fn ensure_encryption_key_registered(&self, key: &EncryptionPublicKey) -> ChainResult<i64> {
        self.store
            .encryption_key_did(key)?
            .ok_or(ChainFailure::Error(ChainError::EncryptionKeyMissing))
    }

    /// `ensure_role_claim` — required-claim gating (GAPS.md §5, P1-11).
    /// An unset role spec means the role is permissionless.
    /// Mediators fall back to the auditor spec when they have none of their own.
    fn ensure_role_claim(&self, identity_id: i64, role: &str) -> ChainResult<()> {
        let spec: Option<(Vec<u8>, Vec<u8>)> = self
            .store
            .conn
            .query_row(
                "SELECT claim, trusted_issuers FROM required_claims WHERE role = ?1",
                params![role],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?;
        let (claim, trusted_blob) = match spec {
            Some(spec) => spec,
            None if role == "Mediator" => self
                .store
                .conn
                .query_row(
                    "SELECT claim, trusted_issuers FROM required_claims WHERE role = 'Auditor'",
                    [],
                    |row| Ok((row.get(0)?, row.get(1)?)),
                )
                .optional()?
                .unwrap_or_default(),
            None => return Ok(()),
        };
        if claim.is_empty() {
            return Ok(());
        }
        let trusted: Vec<i64> =
            codec::Decode::decode(&mut trusted_blob.as_slice()).map_err(ChainFailure::from)?;
        let now = self.store.timestamp()? as i64;
        let has_claim = trusted.iter().any(|issuer| {
            self.store
                .conn
                .query_row(
                    "SELECT 1 FROM claims WHERE identity_id = ?1 AND issuer_identity_id = ?2 AND claim = ?3 AND expiry_moment >= ?4",
                    params![identity_id, issuer, claim, now],
                    |_| Ok(()),
                )
                .is_ok()
        });
        if has_claim {
            Ok(())
        } else {
            Err(ChainFailure::Error(ChainError::MissingRequiredClaim))
        }
    }

    /// `ensure_mediators_registered` (pallet `lib.rs:3881`).
    fn ensure_mediators_registered(
        &self,
        mediators: &[(AccountPublicKey, EncryptionPublicKey)],
    ) -> ChainResult<()> {
        for (acct, enc) in mediators {
            let did = self.ensure_account_registered(acct)?;
            let account_enc = self
                .store
                .account_encryption_key(acct)?
                .ok_or(ChainFailure::Error(ChainError::EncryptionKeyMissing))?;
            if account_enc != *enc {
                // Shared-key mediator path: the asset mediator key must have been distributed to
                // the account's encryption key (`SharedKeyRecipients`).
                let shared: bool = self
                    .store
                    .conn
                    .query_row(
                        "SELECT 1 FROM shared_key_recipients WHERE enc_key = ?1 AND recipient = ?2",
                        params![enc.encode(), account_enc.encode()],
                        |_| Ok(()),
                    )
                    .is_ok();
                if !shared {
                    return Err(ChainFailure::Error(ChainError::EncryptionKeyNotShared));
                }
            }
            self.ensure_role_claim(did, "Mediator")?;
        }
        Ok(())
    }

    /// `ensure_auditors_registered` (pallet `lib.rs:3869`).
    fn ensure_auditors_registered(&self, auditors: &[EncryptionPublicKey]) -> ChainResult<()> {
        for key in auditors {
            let did = self.ensure_encryption_key_registered(key)?;
            self.ensure_role_claim(did, "Auditor")?;
        }
        Ok(())
    }

    /// `get_asset_keys_lookup` (pallet `lib.rs:3842`): build the proof-time asset keys view,
    /// checking existence and the freeze flag.
    fn get_asset_keys_lookup(
        &self,
        asset_ids: impl IntoIterator<Item = AssetId>,
    ) -> ChainResult<AssetKeysLookup> {
        let mut lookup = AssetKeysLookup::new();
        for asset_id in asset_ids {
            let keys = self
                .store
                .asset_keys(asset_id)?
                .ok_or(ChainFailure::Error(ChainError::AssetMissing))?;
            let frozen = self.store.asset_frozen(asset_id)?.is_some();
            if frozen {
                return Err(ChainFailure::Error(ChainError::AssetIsFrozen));
            }
            lookup.add(AssetState {
                asset_id,
                frozen,
                keys,
            });
        }
        Ok(lookup)
    }

    /// Current asset state (keys + freeze flag) for leg building.
    fn asset_state(&self, asset_id: AssetId) -> ChainResult<AssetState> {
        let keys = self
            .store
            .asset_keys(asset_id)?
            .ok_or(ChainFailure::Error(ChainError::AssetMissing))?;
        let frozen = self.store.asset_frozen(asset_id)?.is_some();
        Ok(AssetState {
            asset_id,
            frozen,
            keys,
        })
    }

    /// Public wrapper for tooling and tests that build settlement proofs directly.
    pub fn asset_state_pub(&self, asset_id: AssetId) -> ChainResult<AssetState> {
        self.asset_state(asset_id)
    }

    /// `create_settlement` for a pre-built proof (tests/tooling entry point).
    pub fn create_settlement_verify_pub<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        proof: &SettlementProof<Limits>,
    ) -> ChainResult<SettlementId> {
        self.dispatch("create_settlement", false, |chain| {
            chain.base_create_settlement(proof, rng)
        })
    }

    // ---------------------------------------------------------------- account state update proofs

    /// `handle_account_state_update_proof` (pallet `lib.rs:3580`), chain side:
    /// nullifier uniqueness, root lookup with age check, then the call-specific closure (which
    /// runs the settlement state machine and proof verification), then the leaf insert.
    fn handle_account_state_update(
        &self,
        proof: &impl AccountStateUpdate,
        verify: impl FnOnce(&Self) -> ChainResult<()>,
    ) -> ChainResult<()> {
        // 1. `ensure_account_state_nullifier_unique` — before verification.
        let nullifier = proof.nullifier();
        if self
            .store
            .nullifier_used(TreeKind::Account, &nullifier.encode())?
        {
            return Err(ChainFailure::Error(ChainError::NullifierAlreadyUsed));
        }

        // 2. `get_account_curve_tree_root(proof.root_block())` — missing/expired roots fail here.
        self.store
            .get_block_root(TreeKind::Account, proof.root_block())?
            .ok_or(ChainFailure::Error(ChainError::CurveTreeRootNotFound))?;

        // 3. verify (settlement state machine + proof check inside).
        verify(self)?;

        // 4. insert the new account leaf; burn the nullifier.
        let leaf = proof
            .account_state_commitment()
            .as_leaf_value()
            .map_err(ChainFailure::from)?;
        self.append_account_leaf(leaf, Some(nullifier))?;
        Ok(())
    }

    /// `insert_account_leaf`: allocate the next append-only index and write the leaf.
    /// The root is recomputed at block finalization only (`end_block`), matching
    /// `update_account_curve_tree_root`.
    fn append_account_leaf(
        &self,
        leaf: CompressedLeafValue<AccountTreeConfig>,
        nullifier: Option<AccountStateNullifier>,
    ) -> ChainResult<()> {
        if let Some(nullifier) = nullifier {
            self.store
                .burn_nullifier(TreeKind::Account, &nullifier.encode())?;
        }
        let index = self.store.next_leaf_index(TreeKind::Account)?;
        self.store
            .set_next_leaf_index(TreeKind::Account, index + 1)?;
        self.store
            .set_leaf(TreeKind::Account, index, &leaf.encode(), true)?;
        self.store
            .event("AccountStateLeafInserted", format!("leaf_index={index}"))?;
        Ok(())
    }

    /// Load the prover-side account asset state. Prover state is CLI bookkeeping (GAPS.md §1):
    /// the chain only stores commitments and nullifiers.
    fn prover_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
    ) -> ChainResult<AccountAssetState> {
        self.store
            .prover_account_state(account, asset_id)?
            .ok_or_else(|| {
                ChainFailure::Internal(format!(
                "no account asset state for account/asset {asset_id}; register the account first"
            ))
            })
    }

    fn save_prover_state(
        &self,
        account: &AccountPublicKey,
        asset_id: AssetId,
        state: &AccountAssetState,
    ) -> ChainResult<()> {
        self.store
            .set_prover_account_state(account, asset_id, state)
    }

    // ---------------------------------------------------------------- P0 extrinsics

    /// `register_accounts` (call 0, pallet `lib.rs:1576`).
    pub fn register_accounts<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;
        let did = self.did_for_signer(signer)?;

        let proof =
            if let Some(proof) = proof_action.get_proof::<AccountRegistrationProof<Limits>>()? {
                proof
            } else {
                let proof = AccountRegistrationProof::<Limits>::new(rng, &[keys], &did)
                    .map_err(ChainFailure::from)?;
                proof_action.save_proof(&proof)?;
                proof
            };

        let call = format!("register_accounts({}, {} accounts)", signer, proof.len());
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let caller_identity_id = self.store.identity_id(signer)?;
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            // `T::MaxKeysPerRegProof`
            if proof.len() > chain.store.config.max_keys_per_reg_proof {
                return Err(ChainFailure::Error(ChainError::TooManyProofs));
            }
            for account in &proof.accounts {
                // A fee account with the same key must belong to the caller.
                if let Some(fee_did) = chain.store.fee_account_did(&account.acct)? {
                    if fee_did != caller_identity_id {
                        return Err(ChainFailure::Error(ChainError::NotAccountOwner));
                    }
                }
                if chain.store.account_did(&account.acct)?.is_some() {
                    return Err(ChainFailure::Error(ChainError::AccountAlreadyCreated));
                }
                if chain.store.encryption_key_did(&account.enc)?.is_some() {
                    return Err(ChainFailure::Error(
                        ChainError::EncryptionKeyAlreadyRegistered,
                    ));
                }
                chain
                    .store
                    .insert_account_did(&account.acct, caller_identity_id)?;
                chain
                    .store
                    .insert_did_account(caller_identity_id, &account.acct)?;
                chain
                    .store
                    .insert_encryption_key_did(&account.enc, caller_identity_id)?;
                chain
                    .store
                    .insert_account_encryption_key(&account.acct, &account.enc)?;
                chain
                    .store
                    .insert_encryption_key_account(&account.enc, &account.acct)?;
                chain.store.event(
                    "AccountRegistered",
                    format!(
                        "account={} enc={}",
                        hex::encode(account.acct.encode()),
                        hex::encode(account.enc.encode())
                    ),
                )?;
            }
            proof.verify(&did).map_err(ChainFailure::from)?;
            Ok(())
        });
        if proof_action.apply_proof() && !dry_run {
            self.record_result(
                RecordedOp::RegisterAccounts {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                },
                &result,
            );
        }
        result
    }

    /// `create_asset` (call 2, pallet `lib.rs:1676` / `base_create_asset` at 2817).
    #[allow(clippy::too_many_arguments)]
    pub fn create_asset(
        &self,
        issuer_signer: &str,
        name: &str,
        symbol: &str,
        decimals: u8,
        data: &[u8],
        mediators: &[(AccountPublicKey, EncryptionPublicKey)],
        auditors: &[EncryptionPublicKey],
    ) -> ChainResult<AssetId> {
        let issuer_identity_id = self.store.identity_id(issuer_signer)?;
        let call = format!("create_asset({name})");
        let result = self.dispatch(&call, false, |chain| {
            // Metadata bounds (GAPS.md §1: `InvalidAssetName`/`NameTooLong`/`SymbolTooLong`/`TooManyDecimals`).
            if name.is_empty() {
                return Err(ChainFailure::Error(ChainError::InvalidAssetName));
            }
            if name.len() > MAX_NAME_LEN {
                return Err(ChainFailure::Error(ChainError::NameTooLong));
            }
            if symbol.len() > MAX_SYMBOL_LEN {
                return Err(ChainFailure::Error(ChainError::SymbolTooLong));
            }
            if decimals > MAX_DECIMALS {
                return Err(ChainFailure::Error(ChainError::TooManyDecimals));
            }
            // Asset-creator role gate (`RequiredClaims`, P1-11).
            chain.ensure_role_claim(issuer_identity_id, "AssetCreator")?;
            // Key registration gates (pallet `ensure_mediators_registered`/`ensure_auditors_registered`).
            chain.ensure_mediators_registered(mediators)?;
            chain.ensure_auditors_registered(auditors)?;

            // `NextAssetId`
            let asset_id = chain.store.next_asset_id()?;

            chain
                .store
                .insert_asset(asset_id, name, symbol, decimals, data, issuer_identity_id)?;
            chain
                .store
                .insert_owner_asset(issuer_identity_id, asset_id)?;
            chain.update_asset_leaf(asset_id, mediators, auditors, true, issuer_identity_id)?;
            chain.store.event(
                "AssetCreated",
                format!("asset_id={asset_id} name={name} symbol={symbol} decimals={decimals}"),
            )?;
            Ok(asset_id)
        });
        if result.is_ok() {
            self.record_ok(RecordedOp::CreateAsset {
                signer: issuer_signer.to_string(),
                name: name.to_string(),
                symbol: symbol.to_string(),
                decimals,
                data: hex::encode(data),
                mediators: crate::corpus::encode_hex(&mediators.to_vec()),
                auditors: crate::corpus::encode_hex(&auditors.to_vec()),
            });
        }
        result
    }

    /// `update_asset_leaf` / `recommit_asset_leaf` (pallet `lib.rs:3616`/3655): store the keys,
    /// compute the asset leaf (with the freeze bit), write it at `leaf_index == asset_id`, and
    /// store the asset root for the current block.
    fn update_asset_leaf(
        &self,
        asset_id: AssetId,
        mediators: &[(AccountPublicKey, EncryptionPublicKey)],
        auditors: &[EncryptionPublicKey],
        is_create: bool,
        caller_identity_id: i64,
    ) -> ChainResult<()> {
        if mediators.len() + auditors.len() == 0 {
            return Err(ChainFailure::Error(ChainError::NoAuditorsOrMediators));
        }
        let state = AssetState::new::<Limits>(asset_id, mediators, auditors)
            .map_err(|_| ChainFailure::Error(ChainError::AssetStateInvalid))?;
        // Carry the current freeze flag into the leaf commitment (pallet does the same).
        let frozen = self.store.asset_frozen(asset_id)?.is_some();
        let state = AssetState { frozen, ..state };
        self.store.insert_asset_keys(asset_id, &state.keys)?;
        let leaf = state.commitment().map_err(ChainFailure::from)?;
        let index = asset_id as LeafIndex;
        self.asset_tree
            .clone()
            .tree
            .update_leaf(index, leaf)
            .map_err(ChainFailure::from)?;
        self.store
            .event("AssetStateLeafUpdated", format!("leaf_index={index}"))?;
        if !is_create {
            self.store.event(
                "AssetUpdated",
                format!(
                    "asset_id={asset_id} auditors={} mediators={}",
                    auditors.len(),
                    mediators.len()
                ),
            )?;
            let _ = caller_identity_id;
        }
        Ok(())
    }

    /// `update_asset_keys` (call 24, pallet `lib.rs:2529`).
    pub fn update_asset_keys(
        &self,
        caller_signer: &str,
        asset_id: AssetId,
        mediators: &[(AccountPublicKey, EncryptionPublicKey)],
        auditors: &[EncryptionPublicKey],
    ) -> ChainResult<()> {
        let caller_identity_id = self.store.identity_id(caller_signer)?;
        let call = format!("update_asset_keys({asset_id})");
        let result = self.dispatch(&call, false, |chain| {
            chain.ensure_asset_owner(caller_identity_id, asset_id)?;
            chain.ensure_mediators_registered(mediators)?;
            chain.ensure_auditors_registered(auditors)?;
            chain.update_asset_leaf(asset_id, mediators, auditors, false, caller_identity_id)?;
            Ok(())
        });
        if result.is_ok() {
            self.record_ok(RecordedOp::UpdateAssetKeys {
                signer: caller_signer.to_string(),
                asset_id,
                mediators: crate::corpus::encode_hex(&mediators.to_vec()),
                auditors: crate::corpus::encode_hex(&auditors.to_vec()),
            });
        }
        result
    }

    /// `set_asset_frozen` (call 25, pallet `lib.rs:2543` / `base_set_asset_frozen` at 2635).
    /// `caller_signer == Some(root_signer)` models Root when the CLI is run with the
    /// `--root` origin; issuer freezes require asset ownership.
    pub fn set_asset_frozen(
        &self,
        caller_signer: Option<&str>,
        asset_id: AssetId,
        frozen: bool,
    ) -> ChainResult<()> {
        let caller_identity_id = match caller_signer {
            Some(signer) => Some(self.store.identity_id(signer)?),
            None => None,
        };
        let call = format!("set_asset_frozen({asset_id}, {frozen})");
        let result = self.dispatch(&call, false, |chain| {
            let origin = match caller_identity_id {
                Some(did) => {
                    chain.ensure_asset_owner(did, asset_id)?;
                    "Issuer"
                }
                None => {
                    chain.ensure_asset_exists(asset_id)?;
                    "Root"
                }
            };
            let current = chain.store.asset_frozen(asset_id)?;
            if current.as_deref() == Some("Root") && origin != "Root" {
                return Err(ChainFailure::Error(ChainError::AssetFrozenByRoot));
            }
            let next: Option<&str> = if frozen { Some(origin) } else { None };
            if current.as_deref() == next {
                return Ok(());
            }
            let keys = chain
                .store
                .asset_keys(asset_id)?
                .ok_or(ChainFailure::Error(ChainError::AssetMissing))?;
            chain.store.set_asset_frozen(asset_id, next)?;
            // Recommit the *stored* keys with only the freeze bit changed, exactly like
            // `base_set_asset_frozen` (`Keys::<T>::get` verbatim). Re-deriving mediator keys
            // from `AccountEncryptionKey` would drop a distributed/shared key.
            chain.recommit_asset_leaf(asset_id, &keys, frozen)?;
            chain.store.event(
                if frozen {
                    "AssetFrozen"
                } else {
                    "AssetUnfrozen"
                },
                format!("asset_id={asset_id} origin={origin}"),
            )?;
            Ok(())
        });
        if result.is_ok() {
            self.record_ok(RecordedOp::SetAssetFrozen {
                signer: caller_signer.map(|signer| signer.to_string()),
                asset_id,
                frozen,
            });
        }
        result
    }

    /// `recommit_asset_leaf`: rewrite the asset leaf with the existing key set and a new freeze
    /// bit (`base_set_asset_frozen`).
    fn recommit_asset_leaf(
        &self,
        asset_id: AssetId,
        keys: &AssetKeys,
        frozen: bool,
    ) -> ChainResult<()> {
        let state = AssetState {
            asset_id,
            frozen,
            keys: keys.clone(),
        };
        let leaf = state.commitment().map_err(ChainFailure::from)?;
        self.asset_tree
            .clone()
            .tree
            .update_leaf(asset_id as LeafIndex, leaf)
            .map_err(ChainFailure::from)?;
        self.store
            .event("AssetStateLeafUpdated", format!("leaf_index={asset_id}"))?;
        Ok(())
    }

    /// `register_account_assets` (call 3, pallet `lib.rs:1709`). The CLI builds a
    /// `BatchedAccountAssetRegistrationProof` (the extrinsic's proof type) with the single
    /// (account, asset) pair named on the command line.
    pub fn register_account_assets<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        asset_id: AssetId,
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;
        let did = self.did_for_signer(signer)?;
        let params = get_account_curve_tree_parameters();
        let identity_id = self.store.identity_id(signer)?;
        let public_keys = keys.public_keys();

        let (proof, states) = if let Some(proof) =
            proof_action.get_proof::<BatchedAccountAssetRegistrationProof<Limits>>()?
        {
            (proof, Vec::new())
        } else {
            // Pre-flight the extrinsic's chain guards before generating, so an operation that
            // can never apply (e.g. a negative test replay) does not overwrite the prover state.
            let key_did =
                self.ensure_account_and_enc_key_registered(&public_keys.acct, &public_keys.enc)?;
            if key_did != identity_id {
                return Err(ChainFailure::Error(ChainError::NotAccountOwner));
            }
            self.ensure_asset_exists(asset_id)?;
            if self
                .store
                .account_asset_registered(&public_keys.acct, asset_id)?
            {
                return Err(ChainFailure::Error(
                    ChainError::AccountAssetAlreadyRegistered,
                ));
            }
            let (proof, states) = BatchedAccountAssetRegistrationProof::<Limits>::new(
                rng,
                &[(keys, asset_id, 0, None)],
                &did,
                params,
            )
            .map_err(ChainFailure::from)?;
            proof_action.save_proof(&proof)?;
            // Prover side: remember the initial account asset state.
            for state in &states {
                self.save_prover_state(&state.pk_aff(), state.asset_id(), state)?;
            }
            (proof, states)
        };
        let _ = states;

        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let call = format!(
            "register_account_assets({}, {} proofs)",
            signer,
            proof.len()
        );
        let result = self.dispatch(&call, proof_action.is_dry_run(), |chain| {
            if proof.len() > chain.store.config.max_account_asset_reg_proofs {
                return Err(ChainFailure::Error(ChainError::TooManyProofs));
            }
            let mut seen_account = std::collections::BTreeSet::new();
            let mut seen_asset = std::collections::BTreeSet::new();
            let mut registrations = Vec::new();
            for p in &proof.proofs {
                if !seen_account.contains(&p.account.acct) {
                    seen_account.insert(p.account.acct);
                    let key_did = chain
                        .ensure_account_and_enc_key_registered(&p.account.acct, &p.account.enc)?;
                    if key_did != identity_id {
                        return Err(ChainFailure::Error(ChainError::NotAccountOwner));
                    }
                }
                if !seen_asset.contains(&p.asset_id) {
                    seen_asset.insert(p.asset_id);
                    chain.ensure_asset_exists(p.asset_id)?;
                }
                if chain
                    .store
                    .account_asset_registered(&p.account.acct, p.asset_id)?
                {
                    return Err(ChainFailure::Error(
                        ChainError::AccountAssetAlreadyRegistered,
                    ));
                }
                chain
                    .store
                    .insert_account_asset_registration(&p.account.acct, p.asset_id)?;
                registrations.push((p.account.acct, p.asset_id, p.account_state_commitment));
            }
            // Verify the batched proof; the pallet passes an empty `AssetPkTLookup` (no pk_t tracking).
            proof
                .verify(&did, params, rng, &AssetPkTLookup::new())
                .map_err(ChainFailure::from)?;

            for (account, asset_id, commitment) in registrations {
                let leaf = commitment.as_leaf_value().map_err(ChainFailure::from)?;
                chain.append_account_leaf(leaf, None)?;
                chain.store.event(
                    "AccountAssetRegistered",
                    format!(
                        "account={} asset_id={asset_id}",
                        hex::encode(account.encode())
                    ),
                )?;
            }
            Ok(())
        });
        if proof_action.apply_proof() && !proof_action.is_dry_run() {
            self.record_result(
                RecordedOp::RegisterAccountAssets {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    asset_id,
                    proof: crate::corpus::encode_hex(&proof),
                },
                &result,
            );
        }
        result
    }

    /// `mint_asset` (call 4, pallet `lib.rs:1790`).
    pub fn mint_assets<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        issuer_signer: &str,
        account_name: &str,
        asset_id: AssetId,
        amount: Balance,
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(issuer_signer, account_name)?;
        let keys = account.account_keys()?;
        let public_keys = keys.public_keys();
        let did = self.did_for_signer(issuer_signer)?;
        let identity_id = self.store.identity_id(issuer_signer)?;

        let mut prover_state = self
            .store
            .prover_account_state(&public_keys.acct, asset_id)?;
        let proof = if let Some(proof) =
            proof_action.get_proof::<AssetMintingProof<Limits, AccountTreeConfig>>()?
        {
            proof
        } else {
            // Pre-flight the extrinsic's chain checks so generation fails the way the pallet
            // dispatch would (`NotAssetOwner`, `MaxTotalSupplyExceeded`, …) before spending
            // time on a proof that can never be accepted.
            self.ensure_account_permissions(identity_id, &public_keys.acct, &public_keys.enc)?;
            let details = self.ensure_asset_owner(identity_id, asset_id)?;
            self.check_mint_supply(details.total_supply, amount)?;
            let state = prover_state.as_mut().ok_or_else(|| {
                ChainFailure::Internal(format!(
                    "no account asset state for account/asset {asset_id}; register the account first"
                ))
            })?;
            let proof = AssetMintingProof::<Limits>::new(
                rng,
                &keys,
                &did,
                state,
                &self.account_tree,
                amount,
            )
            .map_err(ChainFailure::from)?;
            proof_action.save_proof(&proof)?;
            // Prover side: mint set the pending state; persist it for the `-r` apply run.
            self.save_prover_state(&public_keys.acct, asset_id, state)?;
            proof
        };

        let call = format!("mint_asset({asset_id}, {amount})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            // `ensure_dart_account_permissions`
            chain.ensure_account_permissions(identity_id, &proof.pk, &proof.pk_enc)?;
            // `ensure_dart_asset_owner`
            let mut details = chain.ensure_asset_owner(identity_id, proof.asset_id)?;
            // `MaxTotalSupply` / overflow checks (pallet `lib.rs:1802-1810`).
            chain.check_mint_supply(details.total_supply, proof.amount)?;
            details.total_supply = details
                .total_supply
                .checked_add(proof.amount)
                .ok_or(ChainFailure::Error(ChainError::MaxTotalSupplyExceeded))?;

            chain.handle_account_state_update(&proof, |chain_inner| {
                let account_tree = chain_inner.account_tree.clone();
                proof
                    .verify(&did, &account_tree, rng)
                    .map_err(ChainFailure::from)
            })?;

            chain
                .store
                .set_asset_total_supply(asset_id, details.total_supply)?;
            chain.store.event(
                "AssetMinted",
                format!(
                    "asset_id={asset_id} amount={amount} total_supply={}",
                    details.total_supply
                ),
            )?;
            Ok(())
        });
        if proof_action.apply_proof() && !dry_run {
            self.record_result(
                RecordedOp::MintAsset {
                    signer: issuer_signer.to_string(),
                    account: account_name.to_string(),
                    asset_id,
                    proof: crate::corpus::encode_hex(&proof),
                },
                &result,
            );
        }
        result?;

        if !dry_run {
            // Host side: if a prover state exists (generation or a prior `-w`), promote its
            // pending state. Replay has none, so it applies recorded proofs without one.
            if let Some(mut state) = prover_state {
                state.commit_pending_state().map_err(ChainFailure::from)?;
                self.save_prover_state(&public_keys.acct, asset_id, &state)?;
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------- fee accounts (P1-8)

    /// `register_fee_accounts` (call 14, pallet `lib.rs:2125`): batch-register fee accounts on the
    /// fee-account tree for the caller, depositing the total amount into the fee pool.
    pub fn register_fee_accounts<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        caller_signer: &str,
        fees: &[(String, String, Balance)],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let caller_identity_id = self.store.identity_id(caller_signer)?;
        let caller_did = self.did_for_signer(caller_signer)?;

        let proof = if let Some(proof) =
            proof_action.get_proof::<BatchedFeeAccountRegistrationProof<Limits>>()?
        {
            proof
        } else {
            let mut sub_proofs = Vec::with_capacity(fees.len());
            for (signer, account_name, amount) in fees {
                Self::check_fee_amount(*amount)?;
                let account = self.find_account(signer, account_name)?;
                let keys = account.account_keys()?;
                let (proof, state) = FeeAccountRegistrationProof::<Limits>::new(
                    rng,
                    &keys.acct,
                    FEE_ASSET_ID,
                    *amount,
                    &caller_did,
                )
                .map_err(ChainFailure::from)?;
                self.store.set_pending_fee_account_state(
                    &keys.acct.public,
                    FEE_ASSET_ID,
                    &state,
                )?;
                sub_proofs.push(proof);
            }
            let proofs = BoundedVec::try_from(sub_proofs)
                .map_err(|_| ChainFailure::Error(ChainError::TooManyProofs))?;
            let proof = BatchedFeeAccountRegistrationProof { proofs };
            proof_action.save_proof(&proof)?;
            proof
        };

        let call = format!("register_fee_accounts({} accounts)", proof.proofs.len());
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            // `MaxFeeAccountRegProofs` (pallet `lib.rs:2134`).
            if proof.len() > chain.store.config.max_fee_account_reg_proofs {
                return Err(ChainFailure::Error(ChainError::TooManyProofs));
            }
            let mut registrations = Vec::with_capacity(proof.proofs.len());
            let mut seen_accounts = std::collections::BTreeSet::new();
            for p in &proof.proofs {
                // `NotAccountOwner` for accounts owned by another identity, `FeeAccountAlreadyRegistered`
                // for fee accounts (including a duplicate inside this batch), `InvalidFeeAssetId`
                // for any asset other than the fee asset.
                if let Some(owner) = chain.store.account_did(&p.account)? {
                    if owner != caller_identity_id {
                        return Err(ChainFailure::Error(ChainError::NotAccountOwner));
                    }
                }
                if !seen_accounts.insert(p.account)
                    || chain.store.fee_account_did(&p.account)?.is_some()
                {
                    return Err(ChainFailure::Error(ChainError::FeeAccountAlreadyRegistered));
                }
                if p.asset_id != FEE_ASSET_ID {
                    return Err(ChainFailure::Error(ChainError::InvalidFeeAssetId));
                }
                Self::check_fee_amount(p.amount)?;
                registrations.push((
                    p.account.clone(),
                    p.amount,
                    p.account_state_commitment.clone(),
                ));
            }
            // Fee-pool deposit (`fee_account_deposit`): total POLYX into the pallet fee account.
            let total = Self::check_fee_amount(proof.total_amount(FEE_ASSET_ID))?;
            chain.store.adjust_fee_pool(
                i64::try_from(total)
                    .map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))?,
            )?;

            // `submit_and_wait(VerifyDartAssetRequest::BatchedFeeAccountRegistration)`.
            for p in &proof.proofs {
                p.verify(&caller_did).map_err(ChainFailure::from)?;
            }

            // `insert_fee_account_leaf` per registration (append-only, no nullifier).
            for (account, amount, commitment) in registrations {
                let leaf = commitment.as_leaf_value().map_err(ChainFailure::from)?;
                chain.append_fee_leaf(leaf, None)?;
                chain
                    .store
                    .insert_fee_account_did(&account, caller_identity_id)?;
                chain.store.event(
                    "FeeAccountUpdated",
                    format!(
                        "account={} is_registration=true amount={amount}",
                        hex::encode(account.encode())
                    ),
                )?;
            }
            Ok(())
        });
        if proof_action.apply_proof() && !dry_run {
            self.record_result(
                RecordedOp::RegisterFeeAccounts {
                    signer: caller_signer.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                },
                &result,
            );
        }
        result?;

        if !dry_run {
            // Host side: the chain accepted the registrations; promote the staged fee states.
            for p in &proof.proofs {
                self.promote_fee_state(&p.account)?;
            }
        }
        Ok(())
    }

    /// `topup_fee_accounts` (call 15, pallet `lib.rs:2202`): batch-top-up fee accounts, verifying
    /// against the fee-account tree root and burning the nullifiers of the replaced states.
    pub fn topup_fee_accounts<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        caller_signer: &str,
        fees: &[(String, String, Balance)],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let caller_identity_id = self.store.identity_id(caller_signer)?;
        let caller_did = self.did_for_signer(caller_signer)?;

        let proof =
            if let Some(proof) = proof_action.get_proof::<BatchedFeeAccountTopupProof<Limits>>()? {
                proof
            } else {
                let mut topups = Vec::with_capacity(fees.len());
                for (signer, account_name, amount) in fees {
                    let account = self.find_account(signer, account_name)?;
                    let keys = account.account_keys()?;
                    let mut state = self
                        .store
                        .prover_fee_account_state(&keys.acct.public, FEE_ASSET_ID)?
                        .ok_or_else(|| {
                            // The prover cannot top up a fee account the chain has never registered.
                            ChainFailure::Error(ChainError::FeeAccountMissing)
                        })?;
                    let proof = FeeAccountTopupProof::<Limits>::new(
                        rng,
                        &keys.acct,
                        &mut state,
                        *amount,
                        &caller_did,
                        &self.fee_tree,
                    )
                    .map_err(ChainFailure::from)?;
                    self.store.set_pending_fee_account_state(
                        &keys.acct.public,
                        FEE_ASSET_ID,
                        &state,
                    )?;
                    topups.push(proof);
                }
                // Prover view of "now": the block of the last stored fee root (see StoreBackend).
                let root_block = self
                    .store
                    .last_root_block(TreeKind::FeeAccount)?
                    .unwrap_or(self.store.block_number()?);
                let proofs = BoundedVec::try_from(topups)
                    .map_err(|_| ChainFailure::Error(ChainError::TooManyProofs))?;
                let proof = BatchedFeeAccountTopupProof { root_block, proofs };
                proof_action.save_proof(&proof)?;
                proof
            };

        let call = format!("topup_fee_accounts({} accounts)", proof.proofs.len());
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            // `MaxFeeAccountTopupProofs` (pallet `lib.rs:2211`).
            if proof.len() > chain.store.config.max_fee_account_topup_proofs {
                return Err(ChainFailure::Error(ChainError::TooManyProofs));
            }
            let mut seen = std::collections::BTreeSet::new();
            let mut topups = Vec::with_capacity(proof.proofs.len());
            for p in &proof.proofs {
                // `FeeAccountMissing` / `NotAccountOwner` / `InvalidFeeAssetId` (pallet `2220-2229`).
                let owner = chain
                    .store
                    .fee_account_did(&p.account)?
                    .ok_or(ChainFailure::Error(ChainError::FeeAccountMissing))?;
                if owner != caller_identity_id {
                    return Err(ChainFailure::Error(ChainError::NotAccountOwner));
                }
                if p.asset_id != FEE_ASSET_ID {
                    return Err(ChainFailure::Error(ChainError::InvalidFeeAssetId));
                }
                Self::check_fee_amount(p.amount)?;
                // In-batch and stored nullifier uniqueness (pallet `2231-2240`).
                if !seen.insert(p.nullifier.encode()) {
                    return Err(ChainFailure::Error(ChainError::NullifierAlreadyUsed));
                }
                if chain
                    .store
                    .nullifier_used(TreeKind::FeeAccount, &p.nullifier.encode())?
                {
                    return Err(ChainFailure::Error(ChainError::NullifierAlreadyUsed));
                }
                topups.push((
                    p.account.clone(),
                    p.amount,
                    p.updated_account_state_commitment.clone(),
                    p.nullifier.clone(),
                ));
            }

            // Fee-pool deposit.
            let total = Self::check_fee_amount(proof.total_amount(FEE_ASSET_ID))?;
            chain.store.adjust_fee_pool(
                i64::try_from(total)
                    .map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))?,
            )?;

            // `get_fee_account_curve_tree_root(root_block)` + verify (root age applies).
            let root_blob = chain
                .store
                .get_block_root(TreeKind::FeeAccount, proof.root_block)?
                .ok_or(ChainFailure::Error(ChainError::CurveTreeRootNotFound))?;
            let root = CompressedCurveTreeRoot::<
                FEE_ACCOUNT_TREE_L,
                FEE_ACCOUNT_TREE_M,
                FeeAccountTreeConfig,
            >::decode(&mut root_blob.as_slice())
            .map_err(ChainFailure::from)?
            .root_node()
            .map_err(ChainFailure::from)?;
            for p in &proof.proofs {
                p.verify(rng, &caller_did, &root)
                    .map_err(ChainFailure::from)?;
            }

            // `insert_fee_account_leaf` per topup: burn the nullifier, append the new leaf.
            for (account, amount, commitment, nullifier) in topups {
                let leaf = commitment.as_leaf_value().map_err(ChainFailure::from)?;
                chain.append_fee_leaf(leaf, Some(nullifier))?;
                chain.store.event(
                    "FeeAccountUpdated",
                    format!(
                        "account={} is_registration=false amount={amount}",
                        hex::encode(account.encode())
                    ),
                )?;
            }
            Ok(())
        });
        if proof_action.apply_proof() && !dry_run {
            self.record_result(
                RecordedOp::TopupFeeAccounts {
                    signer: caller_signer.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                },
                &result,
            );
        }
        result?;

        if !dry_run {
            // Host side: promote the staged fee states that generated the proofs.
            for p in &proof.proofs {
                self.promote_fee_state(&p.account)?;
            }
        }
        Ok(())
    }

    /// Host-side promotion of a staged fee state: commit the pending state, then store it as
    /// current.  Runs only after the chain accepted the transaction.
    fn promote_fee_state(&self, account: &AccountPublicKey) -> ChainResult<()> {
        if let Some(mut state) = self
            .store
            .take_pending_fee_account_state(account, FEE_ASSET_ID)?
        {
            state.commit_pending_state().map_err(ChainFailure::from)?;
            self.store
                .set_current_fee_account_state(account, FEE_ASSET_ID, &state)?;
        }
        Ok(())
    }

    /// `amount_to_balance` (pallet `lib.rs:4249`): the fee amounts must fit the balance type.
    fn check_fee_amount(amount: Balance) -> ChainResult<Balance> {
        if amount > MAX_BALANCE {
            return Err(ChainFailure::Error(ChainError::AmountOverflow));
        }
        Ok(amount)
    }

    /// `insert_fee_account_leaf`: append-only leaf on the fee-account tree; the root is recomputed
    /// at block finalization (`end_block`), same as the account tree.
    fn append_fee_leaf(
        &self,
        leaf: CompressedLeafValue<FeeAccountTreeConfig>,
        nullifier: Option<FeeAccountStateNullifier>,
    ) -> ChainResult<()> {
        if let Some(nullifier) = nullifier {
            self.store
                .burn_nullifier(TreeKind::FeeAccount, &nullifier.encode())?;
        }
        let index = self.store.next_leaf_index(TreeKind::FeeAccount)?;
        self.store
            .set_next_leaf_index(TreeKind::FeeAccount, index + 1)?;
        self.store
            .set_leaf(TreeKind::FeeAccount, index, &leaf.encode(), true)?;
        Ok(())
    }

    /// `mint_asset` supply bounds (pallet `lib.rs:1802-1810`).
    fn check_mint_supply(&self, total_supply: u64, amount: Balance) -> ChainResult<()> {
        if amount > MAX_BALANCE {
            return Err(ChainFailure::Error(ChainError::AmountOverflow));
        }
        let next = total_supply
            .checked_add(amount)
            .ok_or(ChainFailure::Error(ChainError::MaxTotalSupplyExceeded))?;
        if next > self.store.config.max_total_supply {
            return Err(ChainFailure::Error(ChainError::MaxTotalSupplyExceeded));
        }
        Ok(())
    }

    // ---------------------------------------------------------------- settlements

    /// `create_settlement` (call 5, pallet `lib.rs:1852` / `base_create_settlement` at 2902).
    ///
    /// Standalone submissions use an empty proof context; use
    /// [`Self::create_settlement_with_context`] to bind the proof to a relayer batch.
    pub fn create_settlement<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        venue_id: &str,
        legs: Vec<(String, String, String, String, AssetId, Balance)>,
        reveal_asset_id: bool,
        visibility: PartyVisibility,
        public_enc_keys: &[String],
        proof_action: ProofAction,
    ) -> ChainResult<SettlementId> {
        self.create_settlement_with_context(
            rng,
            venue_id,
            legs,
            reveal_asset_id,
            visibility,
            public_enc_keys,
            &[],
            proof_action,
        )
    }

    /// `create_settlement` with a proof context. On-chain the settlement proof is verified
    /// with the batch context when it is submitted through a relayer batch; `fee_ctx` is the
    /// value from `relayer_batch_proof_context(nullifier)`.
    #[allow(clippy::too_many_arguments)]
    pub fn create_settlement_with_context<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        venue_id: &str,
        legs: Vec<(String, String, String, String, AssetId, Balance)>,
        reveal_asset_id: bool,
        visibility: PartyVisibility,
        public_enc_keys: &[String],
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<SettlementId> {
        // P1-12: leg builder options — hidden asset ids, party visibility, and extra
        // public encryption keys that must be able to decrypt the leg.
        let mut extra_enc_keys = Vec::new();
        for signer_account in public_enc_keys {
            let (signer, account) = parse_signer_account_pair(signer_account);
            let keys = self
                .find_account(&signer, &account.unwrap_or_else(|| "0".to_string()))?
                .account_keys()?;
            extra_enc_keys.push(keys.public_keys().enc);
        }
        let mut leg_builders = Vec::new();
        for (sender_signer, sender_account, receiver_signer, receiver_account, asset_id, amount) in
            legs
        {
            let sender = self
                .find_account(&sender_signer, &sender_account)?
                .account_keys()?
                .public_keys();
            let receiver = self
                .find_account(&receiver_signer, &receiver_account)?
                .account_keys()?
                .public_keys();
            let asset = self.asset_state(asset_id)?;
            leg_builders.push(LegBuilder {
                sender,
                receiver,
                asset,
                amount,
                config: LegConfig {
                    reveal_asset_id,
                    visibility,
                },
                public_enc_keys: extra_enc_keys.clone(),
            });
        }

        let proof = if let Some(proof) = proof_action.get_proof::<SettlementProof<Limits>>()? {
            proof
        } else {
            let mut builder = SettlementBuilder::<Limits>::new(venue_id.as_bytes());
            for leg in leg_builders {
                builder = builder.leg(leg);
            }
            let proof = builder
                .encrypt_and_prove_with_context(fee_ctx, rng, &self.asset_tree)
                .map_err(ChainFailure::from)?;
            proof_action.save_proof(&proof)?;
            proof
        };

        if proof.memo.len() > self.store.config.max_settlement_memo_length {
            // The extrinsic parameter is bounded at decode time on-chain, so there is no pallet
            // error for this; keep it harness-local so `--expect-error` is not misled.
            return Err(ChainFailure::Internal(format!(
                "settlement memo is {} bytes, max is {}",
                proof.memo.len(),
                self.store.config.max_settlement_memo_length
            )));
        }

        if !proof_action.apply_proof() {
            // Generation-only: assign the numeric settlement alias and the leg rows it points
            // at (the settlement *state* is only initialized on apply) so the parties can
            // target `-S <id> -l <idx>` while generating their affirmation proofs. The apply
            // path reuses the alias (`INSERT ... ON CONFLICT DO NOTHING`).
            let settlement_ref = proof.settlement_ref();
            let settlement_id = self.store.ensure_settlement_alias(&settlement_ref)?;
            if self.store.settlement_leg(&settlement_ref, 0)?.is_none() {
                for (leg_idx, leg) in proof.legs.iter().enumerate() {
                    self.store.insert_settlement_leg(
                        &settlement_ref,
                        leg_idx as LegId,
                        leg.leg_enc(),
                    )?;
                    // Seed the creation-time mediator snapshot too: mediator proofs are
                    // generated against it before the settlement proof is applied.
                    if let Some(asset_id) = leg.revealed_asset_id() {
                        let keys = self.asset_state_pub(asset_id)?;
                        let mediators: Vec<AccountPublicKey> =
                            keys.keys.mediators.iter().copied().collect();
                        self.store.insert_leg_mediators(
                            &settlement_ref,
                            leg_idx as LegId,
                            &mediators,
                        )?;
                    }
                }
            }
            return Ok(settlement_id);
        }

        let call = format!("create_settlement({} legs)", proof.legs.len());
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.base_create_settlement_with_context(&proof, fee_ctx, rng)
        });
        if proof_action.apply_proof() && !dry_run {
            self.record_result(
                RecordedOp::CreateSettlement {
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result
    }

    /// `base_create_settlement` — the body shared by `create_settlement` and batched paths.
    fn base_create_settlement<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        proof: &SettlementProof<Limits>,
        rng: &mut R,
    ) -> ChainResult<SettlementId> {
        self.base_create_settlement_with_context(proof, &[], rng)
    }

    /// `base_create_settlement` with the batch proof context (`VerifyDartAssetRequest::
    /// CreateSettlement { ctx }`).
    fn base_create_settlement_with_context<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        proof: &SettlementProof<Limits>,
        ctx: &[u8],
        rng: &mut R,
    ) -> ChainResult<SettlementId> {
        // `SettlementMissingLegs` / `SettlementTooManyLegs`
        if proof.legs.is_empty() {
            return Err(ChainFailure::Error(ChainError::SettlementMissingLegs));
        }
        if proof.legs.len() > self.store.config.max_settlement_legs {
            return Err(ChainFailure::Error(ChainError::SettlementTooManyLegs));
        }
        let settlement_ref = proof.settlement_ref();
        // Replay guard: `SettlementState::contains_key` — the `Finalized` tombstone keeps
        // replayed settlement proofs rejected after finalization.
        if self
            .store
            .row_text(
                "SELECT status FROM settlement_state WHERE settlement_ref = ?1",
                params![settlement_ref.0.to_vec()],
            )?
            .is_some()
        {
            return Err(ChainFailure::Error(ChainError::SettlementAlreadyExists));
        }

        let asset_lookup = self.get_asset_keys_lookup(proof.revealed_asset_ids())?;

        // Root lookup with the max-age check for the settlement's asset root.
        self.store
            .get_block_root(TreeKind::Asset, proof.root_block)?
            .ok_or(ChainFailure::Error(ChainError::CurveTreeRootNotFound))?;

        proof
            .verify_with_context(ctx, &self.asset_tree, &asset_lookup, rng)
            .map_err(ChainFailure::from)?;

        // Initialize status storage exactly as the pallet does (`lib.rs:2940-3001`).
        self.store.conn.execute(
            "INSERT INTO settlement_state (settlement_ref, status) VALUES (?1, 'Pending')",
            params![settlement_ref.0.to_vec()],
        )?;
        let settlement_id = self.store.ensure_settlement_alias(&settlement_ref)?;

        let mut pending_affirmations = 0u32;
        for (leg_idx, leg) in proof.legs.iter().enumerate() {
            let leg_idx = leg_idx as LegId;
            let mediator_count: usize = if let Some(asset_id) = leg.revealed_asset_id() {
                // Revealed asset legs snapshot the asset's mediators at creation
                // (`LegMediators`), so later `update_asset_keys` cannot change existing legs.
                let keys = asset_lookup
                    .assets
                    .get(&asset_id)
                    .ok_or(ChainFailure::Error(ChainError::AssetMissing))?;
                let mediators: Vec<AccountPublicKey> = keys.mediators.iter().copied().collect();
                self.store
                    .insert_leg_mediators(&settlement_ref, leg_idx, &mediators)?;
                mediators.len()
            } else {
                leg.mediator_count(&asset_lookup)
                    .map_err(|_| ChainFailure::Error(ChainError::AssetStateInvalid))?
            };
            pending_affirmations = pending_affirmations
                .saturating_add(2)
                .saturating_add(mediator_count as u32);
            self.store
                .insert_leg_status(&settlement_ref, leg_idx, "Sender", "Pending")?;
            self.store
                .insert_leg_status(&settlement_ref, leg_idx, "Receiver", "Pending")?;
            for idx in 0..mediator_count as LegId {
                self.store.insert_leg_status(
                    &settlement_ref,
                    leg_idx,
                    &format!("Mediator({idx})"),
                    "Pending",
                )?;
            }
            self.store
                .insert_settlement_leg(&settlement_ref, leg_idx, leg.leg_enc())?;
        }
        self.store
            .set_pending_affirmations(&settlement_ref, pending_affirmations)?;
        self.store.init_pending_finalizations(&settlement_ref)?;
        self.store.set_memo(&settlement_ref, &proof.memo)?;
        self.store
            .set_leg_count(&settlement_ref, proof.legs.len() as u32)?;
        self.store.event(
            "SettlementCreated",
            format!(
                "settlement={settlement_ref} legs={} asset_root_block={}",
                proof.legs.len(),
                proof.root_block
            ),
        )?;
        Ok(settlement_id)
    }

    /// Resolve a settlement leg for the generation side.
    fn leg_context(
        &self,
        settlement_id: SettlementId,
        leg_index: LegId,
    ) -> ChainResult<(LegRef, LegEncrypted)> {
        let settlement_ref = self.store.resolve_settlement_alias(settlement_id)?;
        let leg_ref = LegRef::new(settlement_ref, leg_index);
        let leg_enc = self
            .store
            .settlement_leg(&settlement_ref, leg_index)?
            .ok_or(ChainFailure::Error(ChainError::LegNotFound))?;
        Ok((leg_ref, leg_enc))
    }

    /// CLI convenience: preview a leg from the named party's view so `--asset`/`--amount`
    /// arguments can be checked against the encrypted leg (GAPS.md §3: leg resolution must
    /// follow the proof, and the CLI args are only an assertion).
    pub fn preview_leg(
        &self,
        settlement_id: SettlementId,
        leg_index: LegId,
        role: LegRole,
        keys: &AccountKeys,
    ) -> ChainResult<Leg> {
        let (_leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
        leg_enc.decrypt(role, keys).map_err(ChainFailure::from)
    }

    // ---------------------------------------------------------------- affirmations

    /// `sender_affirmation` (call 6, pallet `lib.rs:1875` / settlement.rs `sender_affirmation`).
    pub fn sender_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: SenderAffirmationProof<Limits> = if let Some(proof) = proof_action.get_proof()? {
            proof
        } else {
            let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
            let leg = leg_enc
                .decrypt(LegRole::sender(), &keys)
                .map_err(ChainFailure::from)?;
            let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
            let proof = SenderAffirmationProof::<Limits>::new_with_context(
                rng,
                &keys,
                &leg_ref,
                fee_ctx,
                leg.amount(),
                &leg_enc,
                &mut state,
                &self.account_tree,
            )
            .map_err(ChainFailure::from)?;
            proof_action.save_proof(&proof)?;
            self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
            self.store.index_prover_state(
                &proof.nullifier().encode(),
                &keys.public_keys().acct,
                leg.asset_id(),
            )?;
            proof
        };

        let leg_ref = proof.leg_ref;
        let call = format!("sender_affirmation({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_sender_affirmation(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::SenderAffirmation {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// `receiver_affirmation` (call 7, pallet `lib.rs:1898`).
    pub fn receiver_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: ReceiverAffirmationProof<Limits> =
            if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
                let leg = leg_enc
                    .decrypt(LegRole::receiver(), &keys)
                    .map_err(ChainFailure::from)?;
                let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
                let proof = ReceiverAffirmationProof::<Limits>::new_with_context(
                    rng,
                    &keys,
                    &leg_ref,
                    fee_ctx,
                    &leg_enc,
                    leg.amount(),
                    &mut state,
                    &self.account_tree,
                )
                .map_err(ChainFailure::from)?;
                proof_action.save_proof(&proof)?;
                self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
                self.store.index_prover_state(
                    &proof.nullifier().encode(),
                    &keys.public_keys().acct,
                    leg.asset_id(),
                )?;
                proof
            };

        let leg_ref = proof.leg_ref;
        let call = format!("receiver_affirmation({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_receiver_affirmation(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::ReceiverAffirmation {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// `mediator_affirmation` (call 8, pallet `lib.rs:1928` / settlement.rs
    /// `mediator_affirmation`). `key_index` is the mediator's position in the leg's
    /// `LegMediators` snapshot.
    pub fn mediator_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        key_index: MediatorId,
        accept: bool,
        proof_action: ProofAction,
    ) -> ChainResult<()> {
        self.mediator_affirmation_with_context(
            rng,
            signer,
            account_name,
            settlement_id,
            leg_index,
            key_index,
            accept,
            &[],
            proof_action,
        )
    }

    /// `mediator_affirmation` with a proof context (bound to the relayer fee nullifier when
    /// submitted through a relayer batch).
    #[allow(clippy::too_many_arguments)]
    pub fn mediator_affirmation_with_context<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        key_index: MediatorId,
        accept: bool,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: MediatorAffirmationProof<Limits> =
            if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
                if leg_enc.asset_id().map_err(ChainFailure::from)?.is_some() {
                    // Revealed asset id: the mediator set is the creation-time snapshot, and the
                    // proof is bound to the mediator's account key.
                    let mediators = self
                        .store
                        .leg_mediators(&leg_ref.settlement, leg_ref.leg_id)?
                        .ok_or(ChainFailure::Error(ChainError::MissingLegMediators))?;
                    mediators
                        .get(key_index as usize)
                        .ok_or(ChainFailure::Error(ChainError::WrongMediatorId))?;
                    let proof = MediatorAffirmationProof::<Limits>::new_revealed_with_context(
                        rng, &leg_ref, fee_ctx, &keys, key_index, accept,
                    )
                    .map_err(ChainFailure::from)?;
                    proof_action.save_proof(&proof)?;
                    proof
                } else {
                    let med_enc = leg_enc
                        .mediator_encryption(key_index)
                        .map_err(ChainFailure::from)?;
                    let proof = MediatorAffirmationProof::<Limits>::new_with_context(
                        rng, &leg_ref, fee_ctx, &med_enc, &keys, key_index, accept,
                    )
                    .map_err(ChainFailure::from)?;
                    proof_action.save_proof(&proof)?;
                    proof
                }
            };

        let leg_ref = proof.leg_ref;
        let call = format!("mediator_affirmation({leg_ref}, accept={accept})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_mediator_affirmation_with_context(&proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::MediatorAffirmation {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    key_index,
                    accept,
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result
    }

    /// `sender_update_counter` (call 9, pallet `lib.rs:1967`).
    pub fn sender_counter_update<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: SenderCounterUpdateProof<Limits> =
            if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
                let leg = leg_enc
                    .decrypt(LegRole::sender(), &keys)
                    .map_err(ChainFailure::from)?;
                let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
                let proof = SenderCounterUpdateProof::<Limits>::new_with_context(
                    rng,
                    &keys,
                    &leg_ref,
                    fee_ctx,
                    &leg_enc,
                    leg.amount(),
                    &mut state,
                    &self.account_tree,
                )
                .map_err(ChainFailure::from)?;
                proof_action.save_proof(&proof)?;
                self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
                self.store.index_prover_state(
                    &proof.nullifier().encode(),
                    &keys.public_keys().acct,
                    leg.asset_id(),
                )?;
                proof
            };

        let leg_ref = proof.leg_ref;
        let call = format!("sender_update_counter({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_sender_counter_update(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::SenderCounterUpdate {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// `sender_revert_affirmation` (call 10, pallet `lib.rs:2000`).
    pub fn sender_revert_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: SenderRevertAffirmationProof<Limits> =
            if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
                let leg = leg_enc
                    .decrypt(LegRole::sender(), &keys)
                    .map_err(ChainFailure::from)?;
                let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
                let proof = SenderRevertAffirmationProof::<Limits>::new_with_context(
                    rng,
                    &keys,
                    &leg_ref,
                    fee_ctx,
                    leg.amount(),
                    &leg_enc,
                    &mut state,
                    &self.account_tree,
                )
                .map_err(ChainFailure::from)?;
                proof_action.save_proof(&proof)?;
                self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
                self.store.index_prover_state(
                    &proof.nullifier().encode(),
                    &keys.public_keys().acct,
                    leg.asset_id(),
                )?;
                proof
            };

        let leg_ref = proof.leg_ref;
        let call = format!("sender_revert_affirmation({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_sender_revert_affirmation(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::SenderRevertAffirmation {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// `receiver_revert_affirmation` (call 11, pallet `lib.rs:2033`).
    pub fn receiver_revert_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: ReceiverRevertAffirmationProof<Limits> =
            if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
                let leg = leg_enc
                    .decrypt(LegRole::receiver(), &keys)
                    .map_err(ChainFailure::from)?;
                let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
                let proof = ReceiverRevertAffirmationProof::<Limits>::new_with_context(
                    rng,
                    &keys,
                    &leg_ref,
                    fee_ctx,
                    &leg_enc,
                    leg.amount(),
                    &mut state,
                    &self.account_tree,
                )
                .map_err(ChainFailure::from)?;
                proof_action.save_proof(&proof)?;
                self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
                self.store.index_prover_state(
                    &proof.nullifier().encode(),
                    &keys.public_keys().acct,
                    leg.asset_id(),
                )?;
                proof
            };

        let leg_ref = proof.leg_ref;
        let call = format!("receiver_revert_affirmation({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_receiver_revert_affirmation(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::ReceiverRevertAffirmation {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// `receiver_claim` (call 12, pallet `lib.rs:2066`).
    pub fn receiver_claim<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: ReceiverClaimProof<Limits> = if let Some(proof) = proof_action.get_proof()? {
            proof
        } else {
            let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
            let leg = leg_enc
                .decrypt(LegRole::receiver(), &keys)
                .map_err(ChainFailure::from)?;
            let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
            let proof = ReceiverClaimProof::<Limits>::new_with_context(
                rng,
                &keys,
                &leg_ref,
                fee_ctx,
                leg.amount(),
                &leg_enc,
                &mut state,
                &self.account_tree,
            )
            .map_err(ChainFailure::from)?;
            proof_action.save_proof(&proof)?;
            self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
            self.store.index_prover_state(
                &proof.nullifier().encode(),
                &keys.public_keys().acct,
                leg.asset_id(),
            )?;
            proof
        };

        let leg_ref = proof.leg_ref;
        let call = format!("receiver_claim({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_receiver_claim(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::ReceiverClaim {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// `instant_sender_affirmation` (call 19, pallet `lib.rs:2387`).
    pub fn instant_sender_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: InstantSenderAffirmationProof<Limits> =
            if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
                let leg = leg_enc
                    .decrypt(LegRole::sender(), &keys)
                    .map_err(ChainFailure::from)?;
                let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
                let proof = InstantSenderAffirmationProof::<Limits>::new_with_context(
                    rng,
                    &keys,
                    &leg_ref,
                    fee_ctx,
                    leg.amount(),
                    &leg_enc,
                    &mut state,
                    &self.account_tree,
                )
                .map_err(ChainFailure::from)?;
                proof_action.save_proof(&proof)?;
                self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
                self.store.index_prover_state(
                    &proof.nullifier().encode(),
                    &keys.public_keys().acct,
                    leg.asset_id(),
                )?;
                proof
            };

        let leg_ref = proof.leg_ref;
        let call = format!("instant_sender_affirmation({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_instant_sender_affirmation(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::InstantSenderAffirmation {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// `instant_receiver_affirmation` (call 20, pallet `lib.rs:2425`).
    pub fn instant_receiver_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        signer: &str,
        account_name: &str,
        settlement_id: SettlementId,
        leg_index: LegId,
        fee_ctx: &[u8],
        mut proof_action: ProofAction,
    ) -> ChainResult<()> {
        let account = self.find_account(signer, account_name)?;
        let keys = account.account_keys()?;

        let proof: InstantReceiverAffirmationProof<Limits> =
            if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                let (leg_ref, leg_enc) = self.leg_context(settlement_id, leg_index)?;
                let leg = leg_enc
                    .decrypt(LegRole::receiver(), &keys)
                    .map_err(ChainFailure::from)?;
                let mut state = self.prover_state(&keys.public_keys().acct, leg.asset_id())?;
                let proof = InstantReceiverAffirmationProof::<Limits>::new_with_context(
                    rng,
                    &keys,
                    &leg_ref,
                    fee_ctx,
                    leg.amount(),
                    &leg_enc,
                    &mut state,
                    &self.account_tree,
                )
                .map_err(ChainFailure::from)?;
                proof_action.save_proof(&proof)?;
                self.save_prover_state(&keys.public_keys().acct, leg.asset_id(), &state)?;
                self.store.index_prover_state(
                    &proof.nullifier().encode(),
                    &keys.public_keys().acct,
                    leg.asset_id(),
                )?;
                proof
            };

        let leg_ref = proof.leg_ref;
        let call = format!("instant_receiver_affirmation({leg_ref})");
        if !proof_action.apply_proof() {
            // Generation-only: the client has the proof; the chain does not run the extrinsic.
            return Ok(());
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.apply_instant_receiver_affirmation(rng, &proof, fee_ctx)
        });
        if !dry_run {
            self.record_result(
                RecordedOp::InstantReceiverAffirmation {
                    signer: signer.to_string(),
                    account: account_name.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                    fee_ctx: hex::encode(fee_ctx),
                },
                &result,
            );
        }
        result?;

        self.commit_prover_pending_state(&keys, dry_run)
    }

    /// After the chain accepted an account-state update, promote the prover's pending state
    /// (host-side bookkeeping, not chain state).
    fn commit_prover_pending_state(&self, keys: &AccountKeys, dry_run: bool) -> ChainResult<()> {
        if dry_run {
            return Ok(());
        }
        let public_keys = keys.public_keys();
        let states = self.store.pending_prover_states(&public_keys.acct)?;
        for (asset_id, mut state) in states {
            if state.pending_state.is_some() {
                state.commit_pending_state().map_err(ChainFailure::from)?;
                self.store
                    .set_prover_account_state(&public_keys.acct, asset_id, &state)?;
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------- encryption keys (P1-11)

    /// `register_encryption_keys` (call 1, pallet `lib.rs:1640`): generate `count` fresh
    /// auditor/mediator encryption keys and batch-register them for the caller's identity.
    /// The keypairs are kept in the CLI host keystore (`host_enc_keys`) for
    /// `distribute_encryption_key` and asset creation.
    pub fn register_encryption_keys<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        caller_signer: &str,
        count: usize,
        mut proof_action: ProofAction,
    ) -> ChainResult<Vec<i64>> {
        let caller_identity_id = self.store.identity_id(caller_signer)?;
        let caller_did = self.did_for_signer(caller_signer)?;

        let proof = if let Some(proof) =
            proof_action.get_proof::<EncryptionKeyRegistrationProof<Limits>>()?
        {
            proof
        } else {
            let mut keys = Vec::with_capacity(count);
            for _ in 0..count {
                keys.push(polymesh_dart::EncryptionKeyPair::rand(rng).map_err(ChainFailure::from)?);
            }
            // Prover side: the device holds the fresh keys from the moment the proof exists.
            for pair in &keys {
                self.store.insert_host_enc_key(caller_signer, pair)?;
            }
            let proof = EncryptionKeyRegistrationProof::<Limits>::new(rng, &keys, &caller_did)
                .map_err(ChainFailure::from)?;
            proof_action.save_proof(&proof)?;
            proof
        };

        let call = format!("register_encryption_keys({} keys)", proof.len());
        if !proof_action.apply_proof() {
            return Ok(self.store.host_enc_key_ids(caller_signer)?);
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            // `MaxKeysPerRegProof` (pallet `lib.rs:1644`).
            if proof.len() > chain.store.config.max_keys_per_reg_proof {
                return Err(ChainFailure::Error(ChainError::TooManyProofs));
            }
            for key in proof.keys.iter() {
                // `base_register_encryption_key`: `EncryptionKeyAlreadyRegistered`.
                if chain.store.encryption_key_did(key)?.is_some() {
                    return Err(ChainFailure::Error(
                        ChainError::EncryptionKeyAlreadyRegistered,
                    ));
                }
                chain
                    .store
                    .insert_encryption_key_did(key, caller_identity_id)?;
            }
            proof.verify(&caller_did).map_err(ChainFailure::from)?;
            for key in proof.keys.iter() {
                chain.store.event(
                    "EncryptionKeyRegistered",
                    format!(
                        "caller_did={caller_signer} enc_key={}",
                        hex::encode(key.encode())
                    ),
                )?;
            }
            Ok(())
        });
        if !dry_run {
            self.record_result(
                RecordedOp::RegisterEncryptionKeys {
                    signer: caller_signer.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                },
                &result,
            );
        }
        result?;
        let ids = self.store.host_enc_key_ids(caller_signer)?;
        Ok(ids)
    }

    /// `distribute_encryption_key` (call 23, pallet `lib.rs:2512` /
    /// `base_distribute_encryption_key` at 2696): register a shared encryption key and record
    /// the recipients it was distributed to (`SharedKeyRecipients`).
    pub fn distribute_encryption_key<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        caller_signer: &str,
        key_id: Option<i64>,
        recipients: &[(String, String)],
        mut proof_action: ProofAction,
    ) -> ChainResult<Option<i64>> {
        let caller_identity_id = self.store.identity_id(caller_signer)?;
        let caller_did = self.did_for_signer(caller_signer)?;
        let nonce = caller_did.to_vec();
        let tree_params = polymesh_dart::curve_tree::get_account_curve_tree_parameters();

        // The distribution nonce binds the caller DID (like the pallet's
        // `verify(did, params, rng)`), so the `-w`/`-r` file round-trip is consistent.
        let proof = if let Some(proof) = proof_action.get_proof::<KeyDistributionProof<Limits>>()? {
            proof
        } else {
            // `None` generates a fresh host key (the device-side key being distributed);
            // `Some(id)` reuses an unregistered host key from `register-encryption-keys`.
            let key = match key_id {
                Some(id) => self.store.host_enc_key(id)?,
                None => {
                    let fresh =
                        polymesh_dart::EncryptionKeyPair::rand(rng).map_err(ChainFailure::from)?;
                    self.store.insert_host_enc_key(caller_signer, &fresh)?;
                    fresh
                }
            };
            let mut recipient_pks = Vec::with_capacity(recipients.len());
            for (signer, account) in recipients {
                recipient_pks.push(
                    self.find_account(signer, account)?
                        .account_keys()?
                        .public_keys()
                        .enc,
                );
            }
            let proof =
                KeyDistributionProof::<Limits>::new(rng, &key, recipient_pks, &nonce, tree_params)
                    .map_err(ChainFailure::from)?;
            proof_action.save_proof(&proof)?;
            proof
        };
        // The host keystore is a client-side convenience: replay applies the recorded proof
        // without it, so the id is `None` there.
        let key_id = self.store.host_enc_key_id(&proof.public_key)?;

        let call = format!(
            "distribute_encryption_key({} recipients)",
            proof.recipient_pks.len()
        );
        if !proof_action.apply_proof() {
            return Ok(key_id);
        }
        let dry_run = proof_action.is_dry_run();
        let result = self.dispatch(&call, dry_run, |chain| {
            chain.base_distribute_encryption_key(
                caller_signer,
                caller_identity_id,
                &proof,
                &nonce,
                tree_params,
                rng,
            )
        });
        if !dry_run {
            self.record_result(
                RecordedOp::DistributeEncryptionKey {
                    signer: caller_signer.to_string(),
                    proof: crate::corpus::encode_hex(&proof),
                },
                &result,
            );
        }
        result?;
        Ok(key_id)
    }

    /// `base_distribute_encryption_key` (pallet `lib.rs:2696`).
    pub fn base_distribute_encryption_key<R: RngCore + CryptoRng>(
        &self,
        caller_signer: &str,
        caller_identity_id: i64,
        proof: &KeyDistributionProof<Limits>,
        nonce: &[u8],
        tree_params: &polymesh_dart::curve_tree::CurveTreeParameters<
            polymesh_dart::curve_tree::AccountTreeConfig,
        >,
        rng: &mut R,
    ) -> ChainResult<()> {
        let encryption_key = proof.public_key.clone();
        // `NoKeyRecipients` (pallet `2701`).
        if proof.recipient_pks.is_empty() {
            return Err(ChainFailure::Error(ChainError::NoKeyRecipients));
        }
        // Caller must satisfy the Auditor role claim (`ensure_role_claim`).
        self.ensure_role_claim(caller_identity_id, "Auditor")?;
        // `EncryptionKeyAlreadyRegistered` (pallet `2704`).
        if self.store.encryption_key_did(&encryption_key)?.is_some() {
            return Err(ChainFailure::Error(
                ChainError::EncryptionKeyAlreadyRegistered,
            ));
        }
        if proof.recipient_pks.len() > self.store.config.max_key_distribution_recipients {
            return Err(ChainFailure::Error(ChainError::TooManySharedKeyRecipients));
        }
        // Each recipient must have a registered encryption key with the Auditor claim.
        for recipient in proof.recipient_pks.iter() {
            let recipient_did = self.ensure_encryption_key_registered(recipient)?;
            self.ensure_role_claim(recipient_did, "Auditor")?;
        }
        // `submit_and_wait(VerifyDartAssetRequest::KeyDistribution)`.
        proof
            .verify(nonce, tree_params, rng)
            .map_err(ChainFailure::from)?;
        self.store
            .insert_encryption_key_did(&encryption_key, caller_identity_id)?;
        for recipient in proof.recipient_pks.iter() {
            self.store.conn.execute(
                "INSERT OR IGNORE INTO shared_key_recipients (enc_key, recipient) VALUES (?1, ?2)",
                params![encryption_key.encode(), recipient.encode()],
            )?;
        }
        self.store.event(
            "EncryptionKeyDistributed",
            format!(
                "caller_signer={caller_signer} enc_key={} recipients={}",
                hex::encode(encryption_key.encode()),
                proof.recipient_pks.len()
            ),
        )?;
        Ok(())
    }

    // ---------------------------------------------------------------- relayer path (P1-8/9)

    fn account_public_key(&self, signer: &str, account: &str) -> ChainResult<AccountPublicKey> {
        Ok(self
            .find_account(signer, account)?
            .account_keys()?
            .public_keys()
            .acct)
    }

    // ---------------------------------------------------------------- relayer path (P1-8/9)

    /// Preview of the nullifier the relayer's next fee payment of `amount` will burn
    /// (`relayer_batch_proof_context(nullifier)` is what party proofs must bind).
    pub fn relayer_fee_preview(
        &self,
        relayer_signer: &str,
        relayer_account: &str,
        amount: Balance,
    ) -> ChainResult<FeeAccountStateNullifier> {
        let keys = self
            .find_account(relayer_signer, relayer_account)?
            .account_keys()?;
        let mut state = self
            .store
            .prover_fee_account_state(&keys.acct.public, FEE_ASSET_ID)?
            .ok_or(ChainFailure::Error(ChainError::FeeAccountMissing))?;
        let change = state
            .get_payment_state(amount)
            .map_err(ChainFailure::from)?;
        FeeAccountStateNullifier::from_affine(
            change
                .current_state
                .nullifier(&polymesh_dart::dart_gens().account_comm_key()),
        )
        .map_err(ChainFailure::from)
    }

    /// Assemble `FeePaymentWithBatchedProofs`: the relayer's payment proof bound to the batch
    /// hash of `batch` (`identity` = relayer DID, or `None` for a broadcast batch).
    pub fn relayer_batched_proofs_new<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        relayer_signer: &str,
        relayer_account: &str,
        batch: BatchedProofs<Limits>,
        amount: Balance,
        broadcast: bool,
        write: &Path,
    ) -> ChainResult<()> {
        let relayer_did = self.did_for_signer(relayer_signer)?;
        let identity: Option<&[u8]> = if broadcast { None } else { Some(&relayer_did) };
        let keys = self
            .find_account(relayer_signer, relayer_account)?
            .account_keys()?;
        let mut state = self
            .store
            .prover_fee_account_state(&keys.acct.public, FEE_ASSET_ID)?
            .ok_or(ChainFailure::Error(ChainError::FeeAccountMissing))?;
        let proof = FeePaymentWithBatchedProofs::<Limits>::new(
            rng,
            &keys.acct,
            batch,
            &mut state,
            identity,
            amount,
            &self.fee_tree,
        )
        .map_err(ChainFailure::from)?;
        self.store
            .set_pending_fee_account_state(&keys.acct.public, FEE_ASSET_ID, &state)?;
        std::fs::write(write, proof.encode())?;
        Ok(())
    }

    /// `relayer_batched_proofs` (verifier entry calling `verify_fee_payment` +
    /// `process_batched_proofs_atomic`, pallet `lib.rs:3340-3400`): the fee payment is
    /// verified and paid in its own transaction (committed even if the batch fails), then
    /// the batch runs atomically bound to the spent fee nullifier.
    pub fn relayer_batched_proofs_apply<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        relayer_signer: &str,
        relayer_account: &str,
        proof: &FeePaymentWithBatchedProofs<Limits>,
        dry_run: bool,
    ) -> ChainResult<()> {
        let relayer_did = self.did_for_signer(relayer_signer)?;
        let target: Option<&[u8]> = if proof.is_broadcast {
            None
        } else {
            Some(&relayer_did)
        };

        // `EmptyBatchedProofs` / `MaxBatchedProofs` run before the fee payment in the pallet
        // (`lib.rs:3341-3353`), so a rejected batch is not charged.
        if proof.batched_proofs.proofs.is_empty() {
            return Err(ChainFailure::Error(ChainError::EmptyBatchedProofs));
        }
        if proof.batched_proofs.len() > self.store.config.max_batched_proofs {
            return Err(ChainFailure::Error(ChainError::TooManyProofs));
        }

        // 1) Fee payment transaction — committed independently of the batch.
        let batch_hash = proof.fee_payment_ctx(target);
        let fee = &proof.fee_payment;
        self.dispatch("verify_fee_payment", dry_run, |chain| {
            // `InvalidFeeAssetId` + amount bounds (pallet `verify_fee_payment`, lib.rs:3447).
            if fee.asset_id != FEE_ASSET_ID {
                return Err(ChainFailure::Error(ChainError::InvalidFeeAssetId));
            }
            Self::check_fee_amount(fee.amount)?;
            // Nullifier uniqueness for the spent fee state.
            if chain
                .store
                .nullifier_used(TreeKind::FeeAccount, &fee.nullifier.encode())?
            {
                return Err(ChainFailure::Error(ChainError::NullifierAlreadyUsed));
            }
            // `get_fee_account_curve_tree_root(root_block)` runs before verification in the
            // pallet, so a missing/expired root is `CurveTreeRootNotFound`, not `InvalidProof`.
            chain
                .store
                .get_block_root(TreeKind::FeeAccount, fee.root_block)?
                .ok_or(ChainFailure::Error(ChainError::CurveTreeRootNotFound))?;
            // `submit_and_wait(VerifyDartAssetRequest::FeeAccountPayment { ctx, root, proof })`
            // maps every verifier error to `InvalidFeePaymentProof`.
            fee.verify(rng, &batch_hash.0, &chain.fee_tree)
                .map_err(|_| ChainFailure::Error(ChainError::InvalidFeePaymentProof))?;
            // `fee_account_withdraw`: the pool must cover the relayer payout.
            let pool = chain.store.fee_pool_balance()?;
            if pool < fee.amount {
                return Err(ChainFailure::Error(ChainError::InsufficientBalance));
            }
            let amount = i64::try_from(fee.amount)
                .map_err(|_| ChainFailure::Error(ChainError::AmountOverflow))?;
            chain.store.adjust_fee_pool(-amount)?;
            // `insert_fee_account_leaf` for the paid fee state.
            let leaf = fee
                .updated_account_state_commitment
                .as_leaf_value()
                .map_err(ChainFailure::from)?;
            chain.append_fee_leaf(leaf, Some(fee.nullifier.clone()))?;
            chain.store.event(
                "FeePaymentProcessed",
                format!("relayer={relayer_signer} amount={}", fee.amount),
            )?;
            Ok(())
        })?;
        if dry_run {
            // The fee payment above was rolled back; still verify the batch so `--dry-run`
            // covers the whole relayer extrinsic, per the documented semantics.
            let ctx = relayer_batch_proof_context(&fee.nullifier);
            return self.dispatch("relayer_batched_proofs", true, |chain| {
                for p in proof.batched_proofs.proofs.iter() {
                    chain.apply_batched_proof(rng, p, &ctx)?;
                }
                Ok(())
            });
        }
        // The fee is paid even if the batch fails, so the host-side fee state must advance now,
        // before the batch result is known (otherwise the next payment reuses a burned nullifier).
        let acct = self.account_public_key(relayer_signer, relayer_account)?;
        self.promote_fee_state(&acct)?;

        // 2) Batch transaction, bound to the spent fee state. A failure reverts the batch
        //    only — the relayer keeps the fee (pallet `process_batched_proofs_atomic`).
        let ctx = relayer_batch_proof_context(&fee.nullifier);
        let batch_result = self.dispatch("relayer_batched_proofs", false, |chain| {
            for p in proof.batched_proofs.proofs.iter() {
                chain.apply_batched_proof(rng, p, &ctx)?;
            }
            Ok(())
        });
        let outcome = match &batch_result {
            Ok(()) => "Ok".to_string(),
            Err(e) => e.name().to_string(),
        };
        self.store.event(
            "RelayerBatchedProofs",
            format!(
                "relayer_did={} proofs={} amount={} batch_result={}",
                hex::encode(relayer_did),
                proof.batched_proofs.len(),
                fee.amount,
                outcome
            ),
        )?;
        // The event is emitted after the dispatch's own trace was flushed (the pallet emits it
        // at the end of the extrinsic), so attach it to the dispatch row explicitly.
        self.store.flush_pending_events()?;
        self.record_result(
            RecordedOp::RelayerBatchedProofs {
                signer: relayer_signer.to_string(),
                account: relayer_account.to_string(),
                proof: crate::corpus::encode_hex(proof),
            },
            &batch_result,
        );
        if batch_result.is_ok() {
            // The relayer path applies the party proofs directly, so promote their pending
            // prover states too; otherwise the next proof from those accounts reuses a burned
            // nullifier.
            self.promote_batched_prover_states(&proof.batched_proofs)?;
        }
        // Unlike the pallet, the CLI surfaces a failed batch as a command error (so scripts and
        // `--expect-error` can assert on it); the fee remains committed, as on-chain.
        batch_result?;
        Ok(())
    }

    // ---------------------------------------------------------------- P1-9: batched apply bodies
    //
    // Each `apply_*_proof` is the extrinsic's chain-side body (the same code the standalone
    // extrinsics dispatch), so `submit_batched_proofs` runs identical semantics per proof.

    /// `base_sender_affirmation` body (pallet `lib.rs:1913`).
    pub fn apply_sender_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &SenderAffirmationProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &proof.leg_ref)?;
            update.ensure_pending()?;
            let pending = update.party_affirms(LegAffirmParty::Sender, true, false)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            update.check_for_execution(pending)?;
            Ok(())
        })?;
        self.store
            .event("SenderAffirmed", format!("leg_ref={}", proof.leg_ref))?;
        Ok(())
    }

    /// `base_receiver_affirmation` body (pallet `lib.rs:1934`).
    pub fn apply_receiver_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &ReceiverAffirmationProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &proof.leg_ref)?;
            update.ensure_pending()?;
            let pending = update.party_affirms(LegAffirmParty::Receiver, true, false)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            update.check_for_execution(pending)?;
            Ok(())
        })?;
        self.store
            .event("ReceiverAffirmed", format!("leg_ref={}", proof.leg_ref))?;
        Ok(())
    }

    /// `base_mediator_affirmation` body (pallet `lib.rs:1954`); the accept decision is the
    /// proof's own (`proof.accept`), as in the pallet.
    pub fn apply_mediator_affirmation(
        &self,
        proof: &MediatorAffirmationProof<Limits>,
    ) -> ChainResult<()> {
        self.apply_mediator_affirmation_with_context(proof, &[])
    }

    /// `base_mediator_affirmation` with the batch proof context
    /// (`VerifyDartAssetRequest::MediatorAffirmation { ctx }`).
    pub fn apply_mediator_affirmation_with_context(
        &self,
        proof: &MediatorAffirmationProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        let accept = proof.accept;
        let leg_ref = proof.leg_ref;
        let update = Settlement::new(&self.store, &leg_ref)?;
        update.ensure_pending()?;
        let pending =
            update.party_affirms(LegAffirmParty::Mediator(proof.key_index), accept, false)?;
        let leg_enc = update.encrypted_leg()?;
        if proof.is_asset_id_revealed() {
            let mediators = self
                .store
                .leg_mediators(&leg_ref.settlement, leg_ref.leg_id)?
                .ok_or(ChainFailure::Error(ChainError::MissingLegMediators))?;
            let mediator = mediators
                .get(proof.key_index as usize)
                .ok_or(ChainFailure::Error(ChainError::WrongMediatorId))?;
            proof
                .verify_revealed_with_context(ctx, mediator)
                .map_err(ChainFailure::from)?;
        } else {
            let med_enc = leg_enc
                .mediator_encryption(proof.key_index)
                .map_err(ChainFailure::from)?;
            proof
                .verify_with_context(ctx, &med_enc)
                .map_err(ChainFailure::from)?;
        }
        if accept {
            update.check_for_execution(pending)?;
        } else {
            update.reject(pending.finals)?;
        }
        self.store.event(
            if accept {
                "MediatorAffirmed"
            } else {
                "MediatorRejected"
            },
            format!("leg_ref={leg_ref} key_index={}", proof.key_index),
        )?;
        Ok(())
    }

    /// `base_sender_update_counter` body (pallet `lib.rs:1979`).
    pub fn apply_sender_counter_update<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &SenderCounterUpdateProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &proof.leg_ref)?;
            update.ensure_executed()?;
            let pending_final = update.party_finalizes(LegAffirmParty::Sender)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            update.check_for_finalization(pending_final)?;
            Ok(())
        })?;
        self.store
            .event("SenderCounterUpdated", format!("leg_ref={}", proof.leg_ref))?;
        Ok(())
    }

    /// `base_sender_revert_affirmation` body (pallet `lib.rs:2012`).
    pub fn apply_sender_revert_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &SenderRevertAffirmationProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &proof.leg_ref)?;
            let status = update.status();
            update.ensure_revertable()?;
            let pending_final = update.party_finalizes(LegAffirmParty::Sender)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            if status == SettlementStatus::Rejected {
                update.check_for_finalization(pending_final)?;
            } else {
                update.reject(pending_final)?;
            }
            Ok(())
        })?;
        self.store.event(
            "SenderAffirmationReverted",
            format!("leg_ref={}", proof.leg_ref),
        )?;
        Ok(())
    }

    /// `base_receiver_revert_affirmation` body (pallet `lib.rs:2045`).
    pub fn apply_receiver_revert_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &ReceiverRevertAffirmationProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &proof.leg_ref)?;
            let status = update.status();
            update.ensure_revertable()?;
            let pending_final = update.party_finalizes(LegAffirmParty::Receiver)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            if status == SettlementStatus::Rejected {
                update.check_for_finalization(pending_final)?;
            } else {
                update.reject(pending_final)?;
            }
            Ok(())
        })?;
        self.store.event(
            "ReceiverAffirmationReverted",
            format!("leg_ref={}", proof.leg_ref),
        )?;
        Ok(())
    }

    /// `base_receiver_claim` body (pallet `lib.rs:2078`).
    pub fn apply_receiver_claim<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &ReceiverClaimProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &proof.leg_ref)?;
            update.ensure_executed()?;
            let pending_final = update.party_finalizes(LegAffirmParty::Receiver)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            update.check_for_finalization(pending_final)?;
            Ok(())
        })?;
        self.store
            .event("ReceiverClaimed", format!("leg_ref={}", proof.leg_ref))?;
        Ok(())
    }

    /// `base_instant_sender_affirmation` body (pallet `lib.rs:2399`): the last-pending-affirmation
    /// gate runs at extrinsic level, then the affirmation executes and the settlement counter
    /// updates in the same dispatch.
    pub fn apply_instant_sender_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &InstantSenderAffirmationProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        let leg_ref = proof.leg_ref;
        let settlement_ref = leg_ref.settlement;
        self.store
            .ensure_last_pending_affirmation(&settlement_ref, 1)?;
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &leg_ref)?;
            update.ensure_pending()?;
            let pending = update.party_affirms(LegAffirmParty::Sender, true, true)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            update.check_for_execution(pending)?;
            Ok(())
        })?;
        self.store.ensure_settlement_executed(&settlement_ref)?;
        self.store
            .event("SenderAffirmed", format!("leg_ref={leg_ref}"))?;
        self.store
            .event("SenderCounterUpdated", format!("leg_ref={leg_ref}"))?;
        Ok(())
    }

    /// `base_instant_receiver_affirmation` body (pallet `lib.rs:2437`).
    pub fn apply_instant_receiver_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        proof: &InstantReceiverAffirmationProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        let leg_ref = proof.leg_ref;
        let settlement_ref = leg_ref.settlement;
        self.store
            .ensure_last_pending_affirmation(&settlement_ref, 1)?;
        self.handle_account_state_update(proof, |chain| {
            let update = Settlement::new(&chain.store, &leg_ref)?;
            update.ensure_pending()?;
            let pending = update.party_affirms(LegAffirmParty::Receiver, true, true)?;
            let leg_enc = update.encrypted_leg()?;
            let account_tree = chain.account_tree.clone();
            proof
                .verify_with_context(ctx, &leg_enc, &account_tree, rng)
                .map_err(ChainFailure::from)?;
            update.check_for_execution(pending)?;
            Ok(())
        })?;
        self.store.ensure_settlement_executed(&settlement_ref)?;
        self.store
            .event("ReceiverAffirmed", format!("leg_ref={leg_ref}"))?;
        self.store
            .event("ReceiverClaimed", format!("leg_ref={leg_ref}"))?;
        Ok(())
    }

    /// `process_batched_proofs` (pallet `lib.rs:3502`) for one `BatchedProof`.
    pub fn apply_batched_proof<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        proof: &BatchedProof<Limits>,
        ctx: &[u8],
    ) -> ChainResult<()> {
        match proof {
            BatchedProof::CreateSettlement(p) => {
                self.base_create_settlement_with_context(p, ctx, rng)?;
                Ok(())
            }
            BatchedProof::SenderAffirmation(p) => self.apply_sender_affirmation(rng, p, ctx),
            BatchedProof::ReceiverAffirmation(p) => self.apply_receiver_affirmation(rng, p, ctx),
            BatchedProof::MediatorAffirmation(p, legs) => {
                // Only a mediator reject can finalize; the pallet checks the leg count only then.
                if !p.accept {
                    self.store
                        .finalizing_leg_count(&p.leg_ref.settlement, *legs)?;
                }
                self.apply_mediator_affirmation_with_context(p, ctx)
            }
            BatchedProof::SenderCounterUpdate(p, legs) => {
                self.store
                    .finalizing_leg_count(&p.leg_ref.settlement, *legs)?;
                self.apply_sender_counter_update(rng, p, ctx)
            }
            BatchedProof::SenderRevertAffirmation(p, legs) => {
                self.store
                    .finalizing_leg_count(&p.leg_ref.settlement, *legs)?;
                self.apply_sender_revert_affirmation(rng, p, ctx)
            }
            BatchedProof::ReceiverRevertAffirmation(p, legs) => {
                self.store
                    .finalizing_leg_count(&p.leg_ref.settlement, *legs)?;
                self.apply_receiver_revert_affirmation(rng, p, ctx)
            }
            BatchedProof::ReceiverClaim(p, legs) => {
                self.store
                    .finalizing_leg_count(&p.leg_ref.settlement, *legs)?;
                self.apply_receiver_claim(rng, p, ctx)
            }
            BatchedProof::ExecuteInstantSettlement(_) => Err(ChainFailure::Internal(
                "ExecuteInstantSettlement batch proofs are not generated by this CLI".into(),
            )),
            BatchedProof::InstantSenderAffirmation(p, legs) => {
                self.store
                    .finalizing_leg_count(&p.leg_ref.settlement, *legs)?;
                self.apply_instant_sender_affirmation(rng, p, ctx)
            }
            BatchedProof::InstantReceiverAffirmation(p, legs) => {
                self.store
                    .finalizing_leg_count(&p.leg_ref.settlement, *legs)?;
                self.apply_instant_receiver_affirmation(rng, p, ctx)
            }
        }
    }

    /// `submit_batched_proofs` (call 16, pallet `lib.rs:2290`): apply a batch atomically —
    /// every proof runs through the same body as its standalone extrinsic, all inside one
    /// transaction, so one failure reverts the whole batch.
    pub fn submit_batched_proofs<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        proofs: &BatchedProofs<Limits>,
        dry_run: bool,
    ) -> ChainResult<()> {
        // `MaxBatchedProofs` (pallet `lib.rs:2298`).
        if proofs.len() > self.store.config.max_batched_proofs {
            return Err(ChainFailure::Error(ChainError::TooManyProofs));
        }
        let call = format!("submit_batched_proofs({} proofs)", proofs.len());
        let result = self.dispatch(&call, dry_run, |chain| {
            for proof in proofs.proofs.iter() {
                chain.apply_batched_proof(rng, proof, &[])?;
            }
            Ok(())
        });
        if !dry_run {
            self.record_result(
                RecordedOp::SubmitBatchedProofs {
                    batch: crate::corpus::encode_hex(proofs),
                },
                &result,
            );
        }
        result?;
        if !dry_run {
            // Host side: promote exactly the prover states the batch consumed, looked up by
            // the nullifiers the generation paths recorded.
            self.promote_batched_prover_states(proofs)?;
        }
        Ok(())
    }

    /// Host-side promotion for a batch the chain accepted: commit exactly the prover states
    /// whose nullifiers the generation paths recorded. Shared by `submit_batched_proofs` and
    /// the relayer batch, so proving from an account after either path works.
    fn promote_batched_prover_states(&self, proofs: &BatchedProofs<Limits>) -> ChainResult<()> {
        for proof in proofs.proofs.iter() {
            let nullifier = match proof {
                BatchedProof::SenderAffirmation(p) => p.nullifier.encode(),
                BatchedProof::ReceiverAffirmation(p) => p.nullifier.encode(),
                BatchedProof::SenderCounterUpdate(p, _) => p.nullifier.encode(),
                BatchedProof::SenderRevertAffirmation(p, _) => p.nullifier.encode(),
                BatchedProof::ReceiverRevertAffirmation(p, _) => p.nullifier.encode(),
                BatchedProof::ReceiverClaim(p, _) => p.nullifier.encode(),
                BatchedProof::InstantSenderAffirmation(p, _) => p.nullifier.encode(),
                BatchedProof::InstantReceiverAffirmation(p, _) => p.nullifier.encode(),
                _ => continue,
            };
            if let Some((account, asset_id)) = self.store.lookup_prover_state(&nullifier)? {
                if let Some(mut state) = self.store.prover_account_state(&account, asset_id)? {
                    if state.pending_state.is_some() {
                        state.commit_pending_state().map_err(ChainFailure::from)?;
                        self.store
                            .set_prover_account_state(&account, asset_id, &state)?;
                    }
                }
            }
        }
        Ok(())
    }

    // ---------------------------------------------------------------- block hooks

    /// `end-block`: `on_finalize` for the current block, then start the next block.
    ///
    /// 1. commit pending account/fee leaves and store their roots for this block
    ///    (`update_*_curve_tree_root`);
    /// 2. re-stamp roots past `MinCurveTreeRootUpdateInterval` (`curve_tree_min_update`);
    /// 3. advance the chain block and clock (`frame_system` + `pallet_timestamp`);
    /// 4. prune expired roots (`on_initialize` → `curve_tree_pruning`).
    pub fn end_block(&self) -> ChainResult<BlockNumber> {
        let block = self.store.block_number()?;
        let call = format!("end_block({block})");
        self.store.begin_tx()?;
        let result = (|chain: &Self| -> ChainResult<()> {
            chain
                .asset_tree
                .clone()
                .tree
                .commit_leaves_to_tree()
                .map_err(ChainFailure::from)?;
            chain
                .account_tree
                .clone()
                .tree
                .commit_leaves_to_tree()
                .map_err(ChainFailure::from)?;
            chain
                .fee_tree
                .clone()
                .tree
                .commit_leaves_to_tree()
                .map_err(ChainFailure::from)?;
            let mut asset = chain.asset_tree.clone();
            let mut account = chain.account_tree.clone();
            let mut fee = chain.fee_tree.clone();
            asset.min_update()?;
            account.min_update()?;
            fee.min_update()?;
            // Advance the block/clock and prune inside the same transaction: a failure must not
            // leave a finalized block with a half-advanced clock or partial pruning.
            chain.store.advance_block()?;
            for tree in [TreeKind::Asset, TreeKind::Account, TreeKind::FeeAccount] {
                let pruned = chain.store.prune_roots(tree)?;
                if pruned > 0 {
                    log::debug!("pruned {pruned} {tree:?} roots");
                }
            }
            Ok(())
        })(self);
        match result {
            Ok(()) => {
                self.store.commit_tx()?;
                if let Err(trace_err) = self.store.flush_trace(&call, None, Vec::new()) {
                    log::error!("failed to record trace for {call}: {trace_err}");
                }
                self.record_ok(RecordedOp::EndBlock);
                Ok(block)
            }
            Err(e) => {
                self.store.rollback_tx()?;
                if let Err(trace_err) =
                    self.store
                        .flush_trace(&call, Some(e.name()), vec![format!("{e}")])
                {
                    log::error!("failed to record trace for {call}: {trace_err}");
                }
                Err(e)
            }
        }
    }

    pub fn store(&self) -> &Arc<Store> {
        &self.store
    }

    /// Write the current roots of all three trees to `<dir>/block_<n>_<tree>_root.bin`
    /// (GAPS.md §7: outputs go to a run directory, not the CWD).
    pub fn write_roots(&self, dir: &Path, block: BlockNumber) -> ChainResult<()> {
        for (tree, name) in [
            (TreeKind::Asset, "asset"),
            (TreeKind::Account, "account"),
            (TreeKind::FeeAccount, "fee_account"),
        ] {
            if let Some(root) = self.store.current_root(tree)? {
                std::fs::write(
                    dir.join(format!("block_{block}_current_{name}_root.bin")),
                    root,
                )
                .map_err(|e| ChainFailure::Internal(e.to_string()))?;
            }
        }
        Ok(())
    }
}

/// CLI-facing settlement id (`settlement_aliases` rowid). The pallet only has `SettlementRef`;
/// the numeric alias exists so scripts can name settlements.
pub type SettlementId = i64;

/// The pallet's `MAX_NAME_LEN`/`MAX_SYMBOL_LEN`/`MAX_DECIMALS` (asset metadata bounds, from
/// `polymesh_primitives::erc20`, re-exported by `Polymesh/pallets/confidential-assets/src/lib.rs`).
pub const MAX_NAME_LEN: usize = 100;
pub const MAX_SYMBOL_LEN: usize = 20;
pub const MAX_DECIMALS: u8 = 8;

/// Decode a SCALE value and reject trailing bytes, so a proof file cannot carry an arbitrary
/// suffix after a valid value.
pub fn decode_exact<T: DecodeWithMemTracking>(bytes: &[u8], what: &str) -> ChainResult<T> {
    let mut input = bytes;
    let value = T::decode(&mut input)
        .map_err(|e| ChainFailure::Internal(format!("failed to decode {what}: {e}")))?;
    if !input.is_empty() {
        return Err(ChainFailure::Internal(format!(
            "{what}: {} trailing byte(s) after the SCALE value",
            input.len()
        )));
    }
    Ok(value)
}

/// Parse a `--seed` value (hex, optional `0x` prefix).
pub fn parse_seed(hex_seed: &str) -> ChainResult<u64> {
    let trimmed = hex_seed.trim().trim_start_matches("0x");
    u64::from_str_radix(trimmed, 16)
        .map_err(|e| ChainFailure::Internal(format!("invalid --seed {hex_seed}: {e}")))
}

/// Resolve the run seed: an explicit `--seed` wins, else the seed stored by `init`, else a
/// random one. `init` persists the seed in the DB, so every later command defaults to the same
/// base seed and a run can be replayed.
pub fn resolve_run_seed(explicit: Option<&str>, store: &Store) -> ChainResult<u64> {
    match (explicit, store.run_seed()?) {
        (Some(hex_seed), _) => parse_seed(hex_seed),
        (None, Some(stored)) => parse_seed(&stored),
        (None, None) => Ok(rand::random::<u64>()),
    }
}

/// Mix the base seed with observable chain progress so each command draws distinct (but
/// reproducible) material from the same stored seed.
pub fn derive_command_seed(seed: u64, store: &Store) -> ChainResult<u64> {
    Ok(seed
        ^ store.tx_count()?.wrapping_mul(0x9E37_79B9_7F4A_7C15)
        ^ (store.block_number()? as u64).wrapping_mul(0xC2B2_AE3D_27D4_EA4F)
        ^ store.prover_progress()?.wrapping_mul(0xD6E8_FEB8_6659_FD3B))
}

/// Split a `signer-account` string; the CLI reuses this for public-enc-key specifiers.
fn parse_signer_account_pair(s: &str) -> (String, Option<String>) {
    match s.split_once('-') {
        Some((signer, account)) => (signer.to_string(), Some(account.to_string())),
        None => (s.to_string(), None),
    }
}
