//! Record and replay of applied transactions (a "corpus") for regression testing.
//!
//! `--record <FILE>` appends one JSONL record per applied transaction: the proof bytes, the
//! apply-side arguments (origin signer/account, fee context, key material) and the outcome.
//! `replay <FILE>` re-applies the corpus to a fresh database initialized from the corpus
//! header and checks every outcome, so a DART change that breaks an old proof or changes a
//! root/state transition shows up as a mismatch.
//!
//! The corpus models the **chain** view: prover-side generation steps are not recorded. Each
//! proof is stored verbatim, so replay exercises the current verifier on historical proof
//! bytes. This is the same idea as the serialization tests: record once, replay in CI, and
//! treat any mismatch as a compatibility break.
//!
//! Typical use:
//!
//! ```text
//! # record (same --record path on every command of the run, starting with init)
//! dart-testing-cli init --seed 0000000000000001 --record run/corpus.jsonl
//! dart-testing-cli create-signer -n issuer --record run/corpus.jsonl
//! ...
//!
//! # replay against a fresh database
//! dart-testing-cli --database /tmp/replay.db replay run/corpus.jsonl
//! ```
//!
//! For an upgrade test, record with the old release, then run `replay` with the new release.
//! Proofs that the new verifier rejects (or accepts differently) are reported with their
//! sequence number, operation and the expected/actual pallet error.

use std::fs::{self, File, OpenOptions};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::Path;

use codec::{Decode, Encode};
use rand_chacha::ChaChaRng;
use rand_core::{CryptoRng, RngCore, SeedableRng};
use serde::{Deserialize, Serialize};

use polymesh_dart::{
    AccountPublicKey, AccountPublicKeys, AssetId, BatchedProofs, EncryptionPublicKey,
    FeePaymentWithBatchedProofs,
};

use crate::config::TestConfig;
use crate::errors::{ChainFailure, ChainResult};
use crate::{Chain, Limits, ProofAction};

pub const CORPUS_FORMAT: &str = "dart-testing-cli/corpus";
pub const CORPUS_VERSION: u32 = 1;

/// First JSONL line: everything needed to recreate the chain and validate the file.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorpusHeader {
    pub format: String,
    pub version: u32,
    /// Base seed stored by `init` (16 hex digits).
    pub seed: String,
    pub config: TestConfig,
    pub tool_version: String,
}

/// One applied transaction. Proof/SCALE values are hex-encoded so the corpus is text-safe and
/// diffable; replay decodes them with the current types (a format change is a mismatch).
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum RecordedOp {
    CreateSigner {
        name: String,
    },
    CreateAccount {
        signer: String,
        account: String,
        key_seed: String,
        /// SCALE-encoded `AccountPublicKeys`.
        public_keys: String,
    },
    EndBlock,
    CreateAsset {
        signer: String,
        name: String,
        symbol: String,
        decimals: u8,
        /// Hex asset data.
        data: String,
        /// SCALE-encoded `Vec<(AccountPublicKey, EncryptionPublicKey)>`.
        mediators: String,
        /// SCALE-encoded `Vec<EncryptionPublicKey>`.
        auditors: String,
    },
    UpdateAssetKeys {
        signer: String,
        asset_id: AssetId,
        mediators: String,
        auditors: String,
    },
    SetAssetFrozen {
        signer: Option<String>,
        asset_id: AssetId,
        frozen: bool,
    },
    RegisterAccounts {
        signer: String,
        account: String,
        proof: String,
    },
    RegisterAccountAssets {
        signer: String,
        account: String,
        asset_id: AssetId,
        proof: String,
    },
    MintAsset {
        signer: String,
        account: String,
        asset_id: AssetId,
        proof: String,
    },
    RegisterFeeAccounts {
        signer: String,
        proof: String,
    },
    TopupFeeAccounts {
        signer: String,
        proof: String,
    },
    RegisterEncryptionKeys {
        signer: String,
        proof: String,
    },
    DistributeEncryptionKey {
        signer: String,
        proof: String,
    },
    CreateSettlement {
        proof: String,
        /// Hex; empty for a standalone settlement.
        fee_ctx: String,
    },
    SenderAffirmation {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    ReceiverAffirmation {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    MediatorAffirmation {
        signer: String,
        account: String,
        key_index: u8,
        accept: bool,
        proof: String,
        fee_ctx: String,
    },
    SenderCounterUpdate {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    SenderRevertAffirmation {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    ReceiverRevertAffirmation {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    ReceiverClaim {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    InstantSenderAffirmation {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    InstantReceiverAffirmation {
        signer: String,
        account: String,
        proof: String,
        fee_ctx: String,
    },
    SubmitBatchedProofs {
        /// SCALE-encoded `BatchedProofs<Limits>`.
        batch: String,
    },
    RelayerBatchedProofs {
        signer: String,
        account: String,
        /// SCALE-encoded `FeePaymentWithBatchedProofs<Limits>`.
        proof: String,
    },
}

impl RecordedOp {
    /// Short name for reports and logs.
    pub fn label(&self) -> &'static str {
        match self {
            RecordedOp::CreateSigner { .. } => "create_signer",
            RecordedOp::CreateAccount { .. } => "create_account",
            RecordedOp::EndBlock => "end_block",
            RecordedOp::CreateAsset { .. } => "create_asset",
            RecordedOp::UpdateAssetKeys { .. } => "update_asset_keys",
            RecordedOp::SetAssetFrozen { .. } => "set_asset_frozen",
            RecordedOp::RegisterAccounts { .. } => "register_accounts",
            RecordedOp::RegisterAccountAssets { .. } => "register_account_assets",
            RecordedOp::MintAsset { .. } => "mint_asset",
            RecordedOp::RegisterFeeAccounts { .. } => "register_fee_accounts",
            RecordedOp::TopupFeeAccounts { .. } => "topup_fee_accounts",
            RecordedOp::RegisterEncryptionKeys { .. } => "register_encryption_keys",
            RecordedOp::DistributeEncryptionKey { .. } => "distribute_encryption_key",
            RecordedOp::CreateSettlement { .. } => "create_settlement",
            RecordedOp::SenderAffirmation { .. } => "sender_affirmation",
            RecordedOp::ReceiverAffirmation { .. } => "receiver_affirmation",
            RecordedOp::MediatorAffirmation { .. } => "mediator_affirmation",
            RecordedOp::SenderCounterUpdate { .. } => "sender_counter_update",
            RecordedOp::SenderRevertAffirmation { .. } => "sender_revert_affirmation",
            RecordedOp::ReceiverRevertAffirmation { .. } => "receiver_revert_affirmation",
            RecordedOp::ReceiverClaim { .. } => "receiver_claim",
            RecordedOp::InstantSenderAffirmation { .. } => "instant_sender_affirmation",
            RecordedOp::InstantReceiverAffirmation { .. } => "instant_receiver_affirmation",
            RecordedOp::SubmitBatchedProofs { .. } => "submit_batched_proofs",
            RecordedOp::RelayerBatchedProofs { .. } => "relayer_batched_proofs",
        }
    }
}

/// One JSONL line after the header.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Record {
    pub seq: u64,
    pub block: u32,
    /// `Ok` or the pallet error name (`--expect-error`-style).
    pub outcome: String,
    /// Human-readable failure detail, for reports; not compared.
    #[serde(default)]
    pub detail: Option<String>,
    #[serde(flatten)]
    pub op: RecordedOp,
}

/// Appends records to a corpus file. One instance per process; a run attaches one per command.
pub struct Recorder {
    file: BufWriter<File>,
    seq: u64,
}

impl Recorder {
    /// Open (or create) a corpus. An existing file must match the caller's seed/config so
    /// records from different runs cannot be mixed silently. `start_new` is used by `init`:
    /// it refuses an existing corpus, so each recording session gets its own file/snapshot.
    pub fn open(path: &Path, header: &CorpusHeader, start_new: bool) -> ChainResult<Self> {
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent)?;
            }
        }
        if path.exists() && fs::metadata(path)?.len() > 0 {
            if start_new {
                return Err(ChainFailure::Internal(format!(
                    "corpus {} already exists; start a new session with a different --record path \
                     (or remove it)",
                    path.display()
                )));
            }
            let existing = read_header(path)?;
            if existing.format != header.format || existing.version != header.version {
                return Err(ChainFailure::Internal(format!(
                    "corpus {} has format {}/{}; expected {}/{}",
                    path.display(),
                    existing.format,
                    existing.version,
                    header.format,
                    header.version
                )));
            }
            if existing.seed != header.seed {
                return Err(ChainFailure::Internal(format!(
                    "corpus {} was recorded with seed {}; this chain uses {}",
                    path.display(),
                    existing.seed,
                    header.seed
                )));
            }
            if existing.config != header.config {
                return Err(ChainFailure::Internal(format!(
                    "corpus {} was recorded with a different chain config; use a fresh corpus \
                     or the same --config/tree heights",
                    path.display()
                )));
            }
            let seq = read_records(path)?.last().map(|r| r.seq).unwrap_or(0);
            Ok(Self {
                file: BufWriter::new(OpenOptions::new().append(true).open(path)?),
                seq,
            })
        } else {
            let mut file = File::create(path)?;
            serde_json::to_writer(&mut file, header)
                .map_err(|e| ChainFailure::Internal(format!("corpus header: {e}")))?;
            file.write_all(b"\n")?;
            file.flush()?;
            Ok(Self {
                file: BufWriter::new(file),
                seq: 0,
            })
        }
    }

    pub fn record(
        &mut self,
        block: u32,
        op: RecordedOp,
        outcome: String,
        detail: Option<String>,
    ) -> ChainResult<()> {
        self.seq += 1;
        let record = Record {
            seq: self.seq,
            block,
            outcome,
            detail,
            op,
        };
        serde_json::to_writer(&mut self.file, &record)
            .map_err(|e| ChainFailure::Internal(format!("corpus record: {e}")))?;
        self.file.write_all(b"\n")?;
        self.file.flush()?;
        Ok(())
    }
}

/// Read and validate the corpus header (first line).
pub fn read_header(path: &Path) -> ChainResult<CorpusHeader> {
    let file = File::open(path)?;
    let line = BufReader::new(file)
        .lines()
        .next()
        .ok_or_else(|| ChainFailure::Internal(format!("corpus {} is empty", path.display())))??;
    let header: CorpusHeader = serde_json::from_str(&line)
        .map_err(|e| ChainFailure::Internal(format!("corpus header: {e}")))?;
    if header.format != CORPUS_FORMAT {
        return Err(ChainFailure::Internal(format!(
            "corpus {} has format {:?}; expected {:?}",
            path.display(),
            header.format,
            CORPUS_FORMAT
        )));
    }
    if header.version != CORPUS_VERSION {
        return Err(ChainFailure::Internal(format!(
            "corpus {} has version {}; this CLI supports {}",
            path.display(),
            header.version,
            CORPUS_VERSION
        )));
    }
    Ok(header)
}

/// Read every record after the header.
pub fn read_records(path: &Path) -> ChainResult<Vec<Record>> {
    let file = File::open(path)?;
    let mut records = Vec::new();
    for (index, line) in BufReader::new(file).lines().enumerate().skip(1) {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let record: Record = serde_json::from_str(&line).map_err(|e| {
            ChainFailure::Internal(format!("corpus {} line {}: {e}", path.display(), index + 1))
        })?;
        records.push(record);
    }
    Ok(records)
}

#[derive(Debug, Clone)]
pub struct ReplayMismatch {
    pub seq: u64,
    pub op: &'static str,
    pub expected: String,
    pub actual: String,
    pub detail: String,
}

#[derive(Debug, Clone, Default)]
pub struct ReplaySummary {
    pub total: usize,
    pub matched: usize,
    pub mismatches: Vec<ReplayMismatch>,
}

/// Re-apply every record to `chain` (already initialized from the header config, with the
/// header seed stored) and compare each outcome to the recorded one.
pub fn replay(chain: &Chain, path: &Path, fail_fast: bool) -> ChainResult<ReplaySummary> {
    let header = read_header(path)?;
    let seed = crate::parse_seed(&header.seed)?;
    let mut rng = ChaChaRng::seed_from_u64(seed);
    let records = read_records(path)?;
    let mut summary = ReplaySummary::default();
    for record in records {
        let result = apply(chain, &mut rng, &record.op);
        let actual = match &result {
            Ok(()) => "Ok".to_string(),
            Err(e) => e.name().to_string(),
        };
        summary.total += 1;
        if actual == record.outcome {
            summary.matched += 1;
            println!(
                "#{} block {}: {}",
                record.seq,
                record.block,
                record.op.label()
            );
        } else {
            let detail = match &result {
                Ok(()) => "Ok".to_string(),
                Err(e) => format!("{e}"),
            };
            println!(
                "MISMATCH #{} block {}: {} expected={} got={} ({})",
                record.seq,
                record.block,
                record.op.label(),
                record.outcome,
                actual,
                detail
            );
            summary.mismatches.push(ReplayMismatch {
                seq: record.seq,
                op: record.op.label(),
                expected: record.outcome.clone(),
                actual,
                detail,
            });
            if fail_fast {
                break;
            }
        }
    }
    Ok(summary)
}

fn apply<R: RngCore + CryptoRng + Send + Sync + Clone>(
    chain: &Chain,
    rng: &mut R,
    op: &RecordedOp,
) -> ChainResult<()> {
    match op {
        RecordedOp::CreateSigner { name } => chain.create_signer(name).map(|_| ()),
        RecordedOp::CreateAccount {
            signer,
            account,
            key_seed,
            public_keys,
        } => {
            let keys = scale_decode::<AccountPublicKeys>(public_keys, "account public keys")?;
            chain
                .create_account_with_keys(signer, account, key_seed, &keys)
                .map(|_| ())
        }
        RecordedOp::EndBlock => chain.end_block().map(|_| ()),
        RecordedOp::CreateAsset {
            signer,
            name,
            symbol,
            decimals,
            data,
            mediators,
            auditors,
        } => {
            let mediators = scale_decode::<Vec<(AccountPublicKey, EncryptionPublicKey)>>(
                mediators,
                "asset mediators",
            )?;
            let auditors = scale_decode::<Vec<EncryptionPublicKey>>(auditors, "asset auditors")?;
            let data = decode_hex(data, "asset data")?;
            chain
                .create_asset(
                    signer, name, symbol, *decimals, &data, &mediators, &auditors,
                )
                .map(|_| ())
        }
        RecordedOp::UpdateAssetKeys {
            signer,
            asset_id,
            mediators,
            auditors,
        } => {
            let mediators = scale_decode::<Vec<(AccountPublicKey, EncryptionPublicKey)>>(
                mediators,
                "asset mediators",
            )?;
            let auditors = scale_decode::<Vec<EncryptionPublicKey>>(auditors, "asset auditors")?;
            chain.update_asset_keys(signer, *asset_id, &mediators, &auditors)
        }
        RecordedOp::SetAssetFrozen {
            signer,
            asset_id,
            frozen,
        } => chain.set_asset_frozen(signer.as_deref(), *asset_id, *frozen),
        RecordedOp::RegisterAccounts {
            signer,
            account,
            proof,
        } => chain.register_accounts(rng, signer, account, apply_action(proof)?),
        RecordedOp::RegisterAccountAssets {
            signer,
            account,
            asset_id,
            proof,
        } => chain.register_account_assets(rng, signer, account, *asset_id, apply_action(proof)?),
        RecordedOp::MintAsset {
            signer,
            account,
            asset_id,
            proof,
        } => chain.mint_assets(rng, signer, account, *asset_id, 0, apply_action(proof)?),
        RecordedOp::RegisterFeeAccounts { signer, proof } => {
            chain.register_fee_accounts(rng, signer, &[], apply_action(proof)?)
        }
        RecordedOp::TopupFeeAccounts { signer, proof } => {
            chain.topup_fee_accounts(rng, signer, &[], apply_action(proof)?)
        }
        RecordedOp::RegisterEncryptionKeys { signer, proof } => chain
            .register_encryption_keys(rng, signer, 0, apply_action(proof)?)
            .map(|_| ()),
        RecordedOp::DistributeEncryptionKey { signer, proof } => chain
            .distribute_encryption_key(rng, signer, None, &[], apply_action(proof)?)
            .map(|_| ()),
        RecordedOp::CreateSettlement { proof, fee_ctx } => {
            let ctx = decode_hex(fee_ctx, "settlement fee ctx")?;
            chain
                .create_settlement_with_context(
                    rng,
                    "",
                    Vec::new(),
                    true,
                    polymesh_dart::PartyVisibility::FullVisibility,
                    &[],
                    &ctx,
                    apply_action(proof)?,
                )
                .map(|_| ())
        }
        RecordedOp::SenderAffirmation {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.sender_affirmation(rng, signer, account, 0, 0, &ctx, apply_action(proof)?)
        }
        RecordedOp::ReceiverAffirmation {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.receiver_affirmation(rng, signer, account, 0, 0, &ctx, apply_action(proof)?)
        }
        RecordedOp::MediatorAffirmation {
            signer,
            account,
            key_index,
            accept,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.mediator_affirmation_with_context(
                rng,
                signer,
                account,
                0,
                0,
                *key_index,
                *accept,
                &ctx,
                apply_action(proof)?,
            )
        }
        RecordedOp::SenderCounterUpdate {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.sender_counter_update(rng, signer, account, 0, 0, &ctx, apply_action(proof)?)
        }
        RecordedOp::SenderRevertAffirmation {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.sender_revert_affirmation(rng, signer, account, 0, 0, &ctx, apply_action(proof)?)
        }
        RecordedOp::ReceiverRevertAffirmation {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.receiver_revert_affirmation(
                rng,
                signer,
                account,
                0,
                0,
                &ctx,
                apply_action(proof)?,
            )
        }
        RecordedOp::ReceiverClaim {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.receiver_claim(rng, signer, account, 0, 0, &ctx, apply_action(proof)?)
        }
        RecordedOp::InstantSenderAffirmation {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.instant_sender_affirmation(rng, signer, account, 0, 0, &ctx, apply_action(proof)?)
        }
        RecordedOp::InstantReceiverAffirmation {
            signer,
            account,
            proof,
            fee_ctx,
        } => {
            let ctx = decode_hex(fee_ctx, "fee ctx")?;
            chain.instant_receiver_affirmation(
                rng,
                signer,
                account,
                0,
                0,
                &ctx,
                apply_action(proof)?,
            )
        }
        RecordedOp::SubmitBatchedProofs { batch } => {
            let batch = scale_decode::<BatchedProofs<Limits>>(batch, "batched proofs")?;
            chain.submit_batched_proofs(rng, &batch, false)
        }
        RecordedOp::RelayerBatchedProofs {
            signer,
            account,
            proof,
        } => {
            let proof =
                scale_decode::<FeePaymentWithBatchedProofs<Limits>>(proof, "relayer payment")?;
            chain.relayer_batched_proofs_apply(rng, signer, account, &proof, false)
        }
    }
}

fn apply_action(proof: &str) -> ChainResult<ProofAction> {
    Ok(ProofAction::ApplyOnly {
        proof: decode_hex(proof, "proof")?,
        dry_run: false,
    })
}

fn decode_hex(value: &str, what: &str) -> ChainResult<Vec<u8>> {
    hex::decode(value).map_err(|e| ChainFailure::Internal(format!("{what}: bad hex: {e}")))
}

fn scale_decode<T: Decode>(value: &str, what: &str) -> ChainResult<T> {
    let bytes = decode_hex(value, what)?;
    let mut input = bytes.as_slice();
    let decoded = T::decode(&mut input)
        .map_err(|e| ChainFailure::Internal(format!("{what}: decode failed: {e}")))?;
    if !input.is_empty() {
        return Err(ChainFailure::Internal(format!(
            "{what}: {} trailing byte(s) after the SCALE value",
            input.len()
        )));
    }
    Ok(decoded)
}

/// SCALE-encode and hex-encode a value for a corpus record.
pub fn encode_hex<T: Encode>(value: &T) -> String {
    hex::encode(value.encode())
}
