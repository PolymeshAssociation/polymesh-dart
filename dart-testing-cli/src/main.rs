use std::path::{Path, PathBuf};

use anyhow::Result;
use clap::{Parser, Subcommand};
use codec::Encode;
use dart_testing_cli::*;
use polymesh_dart::Balance;
use rand_chacha::ChaChaRng;
use rand_core::{CryptoRng, RngCore, SeedableRng};

#[derive(Parser)]
#[command(name = "dart-testing-cli")]
#[command(about = "Simulates the Confidential Assets pallet off-chain for DART proof review")]
struct Cli {
    /// Path to the SQLite database file
    #[arg(short, long, default_value = "dart_test.db")]
    database: String,

    /// Deterministic RNG seed (16 hex digits, u64). Stored in the DB by `init`, so later
    /// commands replay the same key generation without passing the flag again.
    #[arg(long, global = true)]
    seed: Option<String>,

    /// Directory for generated artifacts (roots, trace). Defaults to the current directory.
    #[arg(long, global = true)]
    run_dir: Option<PathBuf>,

    /// Assert that this dispatch fails with the named pallet error (e.g. `--expect-error NotLastPendingAffirmation`).
    #[arg(long, global = true)]
    expect_error: Option<String>,

    /// Parameter preset: `testing` (default, pallet heights 4/5/5), `production`
    /// (mainnet heights 1/1/1), `ci-runtime` (short root-age windows).
    #[arg(long, global = true, value_enum, default_value = "testing")]
    config: ConfigPreset,

    /// Override the genesis asset tree height.
    #[arg(long, global = true)]
    asset_tree_height: Option<NodeLevel>,

    /// Override the genesis account tree height.
    #[arg(long, global = true)]
    account_tree_height: Option<NodeLevel>,

    /// Override the genesis fee-account tree height.
    #[arg(long, global = true)]
    fee_account_tree_height: Option<NodeLevel>,

    /// Append every applied transaction (proof bytes + outcome) to a replayable JSONL corpus
    #[arg(long, global = true)]
    record: Option<PathBuf>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::ValueEnum, Clone, Copy, Debug)]
enum ConfigPreset {
    /// Pallet defaults (`testing` heights 4/5/5, long root-age windows).
    Testing,
    /// Production heights 1/1/1.
    Production,
    /// Short windows so root age / pruning run out in a few blocks.
    CiRuntime,
}

#[derive(Subcommand)]
enum Commands {
    /// Initialize/reset the simulated chain storage
    Init,

    /// Create a new signer (identity)
    CreateSigner {
        /// Name of the signer
        #[arg(short, long)]
        name: String,
    },

    /// Create a new DART account for a signer
    CreateAccount {
        /// Signer and account name in format signer-account
        #[arg(short, long)]
        signer_account: String,
    },

    /// `register_accounts`: prove and register a DART account key pair.
    AccountRegistration {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `create_asset`
    CreateAsset {
        /// Name of the issuer signer
        #[arg(short, long)]
        signer: String,
        /// Type of auditor/mediator (auditor or mediator)
        #[arg(short = 't', long = "type", value_enum)]
        auditor_type: AuditorType,
        /// Signer and account for the auditor/mediator in format signer-account (defaults to account "0" if not provided)
        #[arg(short = 'a', long = "auditor")]
        auditor_signer_account: String,
        /// Asset name
        #[arg(long, default_value = "asset")]
        name: String,
        /// Asset symbol
        #[arg(long, default_value = "SYM")]
        symbol: String,
        /// Asset decimals
        #[arg(long, default_value = "6")]
        decimals: u8,
    },

    /// End the current block (commit pending leaves, store roots, advance the clock)
    EndBlock,

    /// `register_account_assets`: register a DART account with an asset.
    RegisterAccount {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Asset ID
        #[arg(short, long = "asset")]
        asset_id: AssetId,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `register_fee_accounts` (batch fee-account registration; `-f signer-account:amount` per account)
    RegisterFeeAccounts {
        /// Signer and account of the fee-pool depositor in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Fee accounts in format signer-account:amount (repeatable)
        #[arg(short = 'f', long = "fee-account")]
        fee_accounts: Vec<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `topup_fee_accounts` (batch fee-account topup; `-f signer-account:amount` per account)
    TopupFeeAccounts {
        /// Signer and account of the fee-pool depositor in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Fee accounts in format signer-account:amount (repeatable)
        #[arg(short = 'f', long = "fee-account")]
        fee_accounts: Vec<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `mint_asset` (only asset issuer can do this)
    MintAssets {
        /// Issuer signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Asset ID
        #[arg(short, long = "asset")]
        asset_id: AssetId,
        /// Amount to mint
        #[arg(short = 'm', long)]
        amount: Balance,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `create_settlement`
    CreateSettlement {
        /// Venue ID for the settlement (memo)
        #[arg(short, long)]
        venue_id: String,
        /// Settlement legs in format: sender_signer[-sender_account]:receiver_signer[-receiver_account]:asset_id:amount
        #[arg(short, long = "leg")]
        legs: Vec<String>,
        /// Hide the asset id in the legs (membership proofs instead of revealed ids)
        #[arg(long)]
        hidden_asset_id: bool,
        /// Party visibility for the legs (full, none, sender-sees-receiver, receiver-sees-sender)
        #[arg(long, value_enum)]
        visibility: Option<Visibility>,
        /// Extra signer-accounts whose encryption keys can decrypt the legs (repeatable)
        #[arg(long = "public-enc-key")]
        public_enc_keys: Vec<String>,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding this proof to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `sender_affirmation`
    SenderAffirm {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Optional assertion: the leg must carry this asset
        #[arg(short, long = "asset")]
        asset_id: Option<AssetId>,
        /// Optional assertion: the leg must carry this amount
        #[arg(short = 'm', long)]
        amount: Option<Balance>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `receiver_affirmation`
    ReceiverAffirm {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Optional assertion: the leg must carry this asset
        #[arg(short, long = "asset")]
        asset_id: Option<AssetId>,
        /// Optional assertion: the leg must carry this amount
        #[arg(short = 'm', long)]
        amount: Option<Balance>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `mediator_affirmation`
    MediatorAffirm {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Mediator key index in the leg's mediator snapshot
        #[arg(long, default_value = "0")]
        key_index: MediatorId,
        /// Mediator accepts the settlement (the default when neither flag is given)
        #[arg(short, long, action, conflicts_with = "reject")]
        accept: bool,
        /// Mediator rejects the settlement
        #[arg(long, action)]
        reject: bool,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `sender_update_counter`
    SenderCounterUpdate {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `sender_revert_affirmation` (accepted while Pending or Rejected)
    SenderRevertAffirmation {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `receiver_revert_affirmation` (accepted while Pending or Rejected)
    ReceiverRevertAffirmation {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `receiver_claim`
    ReceiverClaim {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `instant_sender_affirmation` (must be the last pending affirmation)
    InstantSenderAffirmation {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `instant_receiver_affirmation` (must be the last pending affirmation)
    InstantReceiverAffirmation {
        /// Signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Fee-submission context: hex-encoded relayer fee nullifier (from
        /// `relayer-fee-preview`) binding these proofs to a relayer batch
        #[arg(long)]
        relayer_fee_nullifier: Option<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `register_encryption_keys`: generate `--count` fresh encryption keys and register them
    /// for `-s`'s identity; prints the host keystore ids for later distribution
    RegisterEncryptionKeys {
        /// Signer and account owning the keys in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Number of fresh encryption keys to generate and register
        #[arg(short = 'n', long, default_value = "1")]
        count: usize,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `distribute_encryption_key`: distribute host key `-k` to recipient accounts' keys
    DistributeEncryptionKey {
        /// Signer and account distributing the key in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Host keystore key id (printed by register-encryption-keys). Omit to generate a
        /// fresh, unregistered key inline — the pallet requires distributed keys to be
        /// unregistered until `distribute_encryption_key` registers them.
        #[arg(short = 'k', long)]
        key_id: Option<i64>,
        /// Recipient signer-accounts (repeatable)
        #[arg(short = 'R', long = "recipient")]
        recipients: Vec<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `update_asset_keys`: replace an asset's mediators/auditors (issuer only)
    UpdateAssetKeys {
        /// Signer and account of the issuer in format signer-account
        #[arg(short, long)]
        signer: String,
        /// Asset ID
        #[arg(short, long = "asset")]
        asset_id: AssetId,
        /// Type of auditor/mediator (auditor or mediator)
        #[arg(short = 't', long = "type", value_enum)]
        auditor_type: AuditorType,
        /// Signer and account for the new auditor/mediator in format signer-account
        #[arg(short = 'a', long = "auditor")]
        auditor_signer_account: String,
    },

    /// `freeze_asset` / `unfreeze_asset`: set the asset's freeze flag (issuer or `--root`)
    SetAssetFrozen {
        /// Asset ID
        #[arg(short, long = "asset")]
        asset_id: AssetId,
        /// Freeze the asset
        #[arg(long)]
        freeze: bool,
        /// Unfreeze the asset
        #[arg(long)]
        unfreeze: bool,
        /// Signer of the issuing identity (required unless `--root`)
        #[arg(short, long)]
        signer: Option<String>,
        /// Act as the governance root origin
        #[arg(long)]
        root: bool,
    },

    /// Preview the relayer fee nullifier the next payment of `-m amount` burns; parties bind
    /// it via `--relayer-fee-nullifier`
    RelayerFeePreview {
        /// Relayer signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Fee amount the payment will spend
        #[arg(short = 'm', long)]
        amount: Balance,
    },

    /// `relayer_batched_proofs`: pay a fee for a batch of proofs (assemble with `-p`/`-w`,
    /// apply with `-r`). Fee is committed even if the batch fails.
    RelayerBatchedProofs {
        /// Relayer signer and account in format signer-account
        #[arg(short, long)]
        signer_account: String,
        /// Proof files to assemble, each in `type=path` form (see submit-batched-proofs)
        #[arg(short, long = "proof")]
        proofs: Vec<String>,
        /// Fee paid out of the pool to the relayer
        #[arg(short = 'm', long)]
        amount: Option<Balance>,
        /// Anyone may submit: bind the fee to no identity
        #[arg(long)]
        broadcast: bool,
        /// Write the assembled FeePaymentWithBatchedProofs to a file
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read a previously assembled FeePaymentWithBatchedProofs file and apply it
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// `submit_batched_proofs`: assemble `-p type=path` proof files into a batch (`-w`),
    /// apply a batch (`-r`), or assemble+apply in one go.
    SubmitBatchedProofs {
        /// Proof files to assemble, each in `type=path` form. Types: create-settlement,
        /// sender-affirm, receiver-affirm, mediator-affirm, sender-counter-update,
        /// sender-revert, receiver-revert, receiver-claim, instant-sender-affirm,
        /// instant-receiver-affirm
        #[arg(short, long = "proof")]
        proofs: Vec<String>,
        /// Write the assembled BatchedProofs to a file
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read a previously assembled BatchedProofs file and apply it
        #[arg(short, long)]
        read: Option<PathBuf>,
        /// Verify without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// List all signers
    ListSigners,

    /// List DART accounts
    ListAccounts {
        /// Optional signer name to filter by
        #[arg(short, long)]
        signer: Option<String>,
    },

    /// List assets
    ListAssets,

    /// List registered fee accounts and the fee pool balance
    ListFeeAccounts,

    /// Get settlement status
    GetSettlement {
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
    },

    /// Show per-party leg affirmation statuses for a settlement
    ShowLegs {
        /// Settlement ID
        #[arg(short = 'S', long)]
        settlement_id: SettlementId,
    },

    /// Dump the chain storage view (block, trees, roots, assets, accounts, settlements, fees)
    ShowStorage,

    /// Show the dispatch/event trace
    Trace,

    /// Replay a recorded corpus against a fresh scratch database and check every outcome
    Replay {
        /// Corpus file written by `--record`
        corpus: PathBuf,
        /// Database file for the replay (default: `<corpus>.replay.db`; the main --database
        /// is not touched)
        #[arg(long)]
        replay_db: Option<PathBuf>,
        /// Keep replaying after a mismatch (report all of them instead of stopping at the first)
        #[arg(long)]
        continue_on_error: bool,
    },
}

#[derive(clap::ValueEnum, Clone, Copy, Debug)]
enum Visibility {
    Full,
    None,
    SenderSeesReceiver,
    ReceiverSeesSender,
}

#[derive(clap::ValueEnum, Clone, Debug)]
enum AuditorType {
    Auditor,
    Mediator,
}

fn main() -> Result<()> {
    env_logger::init();

    let cli = Cli::parse();
    let run_dir = cli.run_dir.clone().unwrap_or_else(|| PathBuf::from("."));
    std::fs::create_dir_all(&run_dir)?;

    // Replay is special: it derives its own scratch DB from the corpus, so it never touches
    // `--database`. The corpus header supplies the seed and chain config.
    if let Commands::Replay {
        corpus,
        replay_db,
        continue_on_error,
    } = &cli.command
    {
        return run_replay(
            &cli.database,
            corpus,
            replay_db.as_deref(),
            &run_dir,
            *continue_on_error,
        );
    }

    let config = build_config(&cli);

    let mut db = Chain::open(&cli.database, config.clone())?;

    // Seed resolution: explicit flag > seed stored by `init` > random. `init` persists the
    // resolved seed, so later commands default to the same base seed.
    let seed = dart_testing_cli::resolve_run_seed(cli.seed.as_deref(), db.store())?;
    // Mix in chain progress so each command run of a scenario draws distinct (yet reproducible)
    // random material — `create-account` twice with the same seed must not derive the same key.
    let derived_seed = dart_testing_cli::derive_command_seed(seed, db.store())?;
    let mut rng = ChaChaRng::seed_from_u64(derived_seed);

    let record_path = cli.record.clone();
    let is_init = matches!(cli.command, Commands::Init);
    if let (Some(path), false) = (record_path.as_deref(), is_init) {
        db.attach_recorder(path)?;
    }

    let result: ChainResult<()> = run_command(&mut db, &cli, &mut rng, &run_dir, config);

    if let (Some(path), true) = (record_path.as_deref(), is_init) {
        if result.is_ok() {
            // The header carries the seed `init` actually stored; a new session gets a new file.
            db.attach_recorder_new(path)?;
        }
    }
    if let Some(corpus) = record_path.as_deref() {
        // Keep a chain snapshot next to the corpus (`corpus.jsonl` -> `corpus.db`), separate
        // from the main `--database`, so recording sessions survive a main-DB reset and can be
        // opened by another release for upgrade tests.
        let session_db = corpus.with_extension("db");
        if result.is_ok() || !is_init {
            if let Err(e) = db.store().snapshot_to(&session_db) {
                eprintln!(
                    "warning: could not write the session database {}: {e}",
                    session_db.display()
                );
            }
        }
    }

    match result {
        Ok(()) => {
            if let Some(expected) = &cli.expect_error {
                eprintln!("expected error {expected}, command succeeded");
                std::process::exit(1);
            }
            write_trace(db.store(), &run_dir)?;
            Ok(())
        }
        Err(failure) => {
            let name = failure.name().to_string();
            write_trace(db.store(), &run_dir)?;
            if let Some(expected) = &cli.expect_error {
                if *expected == name {
                    println!("OK: {name} ({failure})");
                    return Ok(());
                }
                eprintln!("expected error {expected}, got {name}: {failure}");
                std::process::exit(1);
            }
            Err(anyhow::anyhow!("{failure}"))
        }
    }
}

/// Replay a corpus against its own scratch DB (`<corpus>.replay.db` unless overridden). The
/// main `--database` is never opened or reset.
fn run_replay(
    main_db: &str,
    corpus: &Path,
    replay_db: Option<&Path>,
    run_dir: &Path,
    continue_on_error: bool,
) -> Result<()> {
    let header = dart_testing_cli::corpus::read_header(corpus)?;
    let replay_db = replay_db
        .map(PathBuf::from)
        .unwrap_or_else(|| corpus.with_extension("replay.db"));
    if replay_db.as_path() == Path::new(main_db) {
        return Err(anyhow::anyhow!(
            "replay DB {} is the main --database; choose another --replay-db",
            replay_db.display()
        ));
    }
    if replay_db.exists() {
        std::fs::remove_file(&replay_db)?;
    }
    let chain = Chain::open(&replay_db, header.config.clone())?;
    chain.initialize()?;
    chain.store().set_run_seed(&header.seed)?;
    println!(
        "Replaying {} (seed {}) into {}",
        corpus.display(),
        header.seed,
        replay_db.display()
    );
    let summary = dart_testing_cli::corpus::replay(&chain, corpus, !continue_on_error)?;
    write_trace(chain.store(), run_dir)?;
    println!(
        "Replayed {} transactions: {} matched, {} mismatched",
        summary.total,
        summary.matched,
        summary.mismatches.len()
    );
    for mismatch in &summary.mismatches {
        eprintln!(
            "#{} {}: expected {}, got {} ({})",
            mismatch.seq, mismatch.op, mismatch.expected, mismatch.actual, mismatch.detail
        );
    }
    if summary.mismatches.is_empty() {
        Ok(())
    } else {
        std::process::exit(1)
    }
}

fn build_config(cli: &Cli) -> TestConfig {
    let mut config = match cli.config {
        ConfigPreset::Testing => TestConfig::default(),
        ConfigPreset::Production => TestConfig {
            asset_tree_height: 1,
            account_tree_height: 1,
            fee_account_tree_height: 1,
            ..TestConfig::default()
        },
        ConfigPreset::CiRuntime => TestConfig::ci_runtime(),
    };
    if let Some(h) = cli.asset_tree_height {
        config.asset_tree_height = h;
    }
    if let Some(h) = cli.account_tree_height {
        config.account_tree_height = h;
    }
    if let Some(h) = cli.fee_account_tree_height {
        config.fee_account_tree_height = h;
    }
    config
}

fn write_trace(store: &Store, run_dir: &Path) -> ChainResult<()> {
    use std::io::Write as _;
    let traces = store.read_trace()?;
    let file = std::fs::File::create(run_dir.join("trace.jsonl"))?;
    let mut file = std::io::BufWriter::new(file);
    for trace in traces {
        let events: Vec<serde_json::Value> = trace
            .events
            .iter()
            .map(|(e, d)| serde_json::json!({"event": e, "detail": d}))
            .collect();
        let line = serde_json::json!({
            "id": trace.id,
            "block": trace.block,
            "moment": trace.moment,
            "call": trace.call,
            "outcome": trace.outcome,
            "error": trace.error,
            "events": events,
        });
        serde_json::to_writer(&mut file, &line)
            .map_err(|e| ChainFailure::Internal(e.to_string()))?;
        file.write_all(b"\n")?;
    }
    file.flush()?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn run_command<R: RngCore + CryptoRng + Send + Sync + Clone>(
    db: &mut Chain,
    cli: &Cli,
    rng: &mut R,
    run_dir: &Path,
    config: TestConfig,
) -> ChainResult<()> {
    let cli_args = cli;
    match &cli_args.command {
        Commands::Init => {
            db.initialize()?;
            // Persist the seed so every later command defaults to it (replayable runs). `--seed`
            // is normalized to 16 hex digits; without it, a random seed is stored and printed.
            let seed = match cli_args.seed.as_deref() {
                Some(hex_seed) => dart_testing_cli::parse_seed(hex_seed)?,
                None => rand::random::<u64>(),
            };
            let seed = format!("{seed:016x}");
            db.store().set_run_seed(&seed)?;
            db.store()
                .set_config_value("preset", &format!("{:?}", cli_args.config))?;
            println!(
                "Chain initialized (preset {:?}, asset height {}, account height {}, fee height {}, seed {})",
                cli_args.config,
                config.asset_tree_height,
                config.account_tree_height,
                config.fee_account_tree_height,
                seed
            );
        }

        Commands::CreateSigner { name } => {
            let id = db.create_signer(name)?;
            println!("Created signer: {name} (ID: {id})");
        }

        Commands::CreateAccount { signer_account } => {
            let (signer, account) = parse_signer_account(signer_account);
            let account_name = account.ok_or_else(|| {
                ChainFailure::Internal("Account name is required for CreateAccount".into())
            })?;
            let account_info = db.create_account(rng, &signer, &account_name)?;
            println!(
                "Created account '{}' for signer '{}' (ID: {})",
                account_info.name, signer, account_info.id
            );
        }

        Commands::AccountRegistration {
            signer_account,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = parse_signer_account(signer_account);
            let account = account.ok_or_else(|| {
                ChainFailure::Internal("Account name is required for AccountRegistration".into())
            })?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.register_accounts(rng, &signer, &account, proof_action)?;
            println!("Registered account '{signer}:{account}'");
        }

        Commands::CreateAsset {
            signer,
            auditor_type,
            auditor_signer_account,
            name,
            symbol,
            decimals,
        } => {
            let (issuer_signer, _) = parse_signer_account(signer);
            let (auditor_signer, auditor_account) = parse_signer_account(auditor_signer_account);
            let auditor_account = auditor_account.unwrap_or_else(|| "0".to_string());
            let auditor_keys = db
                .find_account(&auditor_signer, &auditor_account)?
                .account_keys()?
                .public_keys();

            let (auditors, mediators) = match auditor_type {
                AuditorType::Auditor => (vec![auditor_keys.enc], vec![]),
                AuditorType::Mediator => (vec![], vec![(auditor_keys.acct, auditor_keys.enc)]),
            };

            let asset_id = db.create_asset(
                &issuer_signer,
                name,
                symbol,
                *decimals,
                &[],
                &mediators,
                &auditors,
            )?;
            println!(
                "Created asset {asset_id} with issuer '{issuer_signer}' and {} '{auditor_signer}:{auditor_account}'",
                match auditor_type {
                    AuditorType::Auditor => "auditor",
                    AuditorType::Mediator => "mediator",
                }
            );
        }

        Commands::EndBlock => {
            let block = db.end_block()?;
            db.write_roots(run_dir, block)?;
            println!(
                "Block {block} finalized; roots written to {}",
                run_dir.display()
            );
        }

        Commands::RegisterAccount {
            signer_account,
            asset_id,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(db, signer_account, Some(*asset_id))?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.register_account_assets(rng, &signer, &account, *asset_id, proof_action)?;
            println!("Registered account '{signer}:{account}' with asset {asset_id}");
        }

        Commands::MintAssets {
            signer_account,
            asset_id,
            amount,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(db, signer_account, Some(*asset_id))?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.mint_assets(rng, &signer, &account, *asset_id, *amount, proof_action)?;
            println!("Minted {amount} units of asset {asset_id} for account '{signer}:{account}'");
        }

        Commands::RegisterFeeAccounts {
            signer_account,
            fee_accounts,
            write,
            read,
            dry_run,
        } => {
            let (signer, _) = parse_signer_account(signer_account);
            let fees = parse_fee_accounts(fee_accounts)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.register_fee_accounts(rng, &signer, &fees, proof_action)?;
            println!(
                "Registered {} fee accounts for '{signer}'; fee pool {}",
                fees.len(),
                db.store().fee_pool_balance()?
            );
        }

        Commands::TopupFeeAccounts {
            signer_account,
            fee_accounts,
            write,
            read,
            dry_run,
        } => {
            let (signer, _) = parse_signer_account(signer_account);
            let fees = parse_fee_accounts(fee_accounts)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.topup_fee_accounts(rng, &signer, &fees, proof_action)?;
            println!(
                "Topped up {} fee accounts for '{signer}'; fee pool {}",
                fees.len(),
                db.store().fee_pool_balance()?
            );
        }

        Commands::RegisterEncryptionKeys {
            signer_account,
            count,
            write,
            read,
            dry_run,
        } => {
            let (signer, _) = parse_signer_account(signer_account);
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            let ids = db.register_encryption_keys(rng, &signer, *count, proof_action)?;
            println!(
                "Registered {count} encryption keys for '{signer}'; host key ids: {}",
                ids.iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            );
        }

        Commands::DistributeEncryptionKey {
            signer_account,
            key_id,
            recipients,
            write,
            read,
            dry_run,
        } => {
            let (signer, _) = parse_signer_account(signer_account);
            let mut recpients = Vec::new();
            for acc in recipients {
                let (s, a) = parse_signer_account(acc);
                recpients.push((s, a.unwrap_or_else(|| "0".to_string())));
            }
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            let key_id = db.distribute_encryption_key(
                rng,
                &signer,
                key_id.as_ref().copied(),
                &recpients,
                proof_action,
            )?;
            println!(
                "Distributed host key {} of '{signer}' to {} recipients",
                key_id
                    .map(|id| id.to_string())
                    .unwrap_or_else(|| "(not in host keystore)".to_string()),
                recpients.len()
            );
        }

        Commands::UpdateAssetKeys {
            signer,
            asset_id,
            auditor_type,
            auditor_signer_account,
        } => {
            let (issuer_signer, _) = parse_signer_account(signer);
            let (auditor_signer, auditor_account) = parse_signer_account(auditor_signer_account);
            let auditor_account = auditor_account.unwrap_or_else(|| "0".to_string());
            let auditor_keys = db
                .find_account(&auditor_signer, &auditor_account)?
                .account_keys()?
                .public_keys();
            let (auditors, mediators) = match auditor_type {
                AuditorType::Auditor => (vec![auditor_keys.enc], vec![]),
                AuditorType::Mediator => (vec![], vec![(auditor_keys.acct, auditor_keys.enc)]),
            };
            db.update_asset_keys(&issuer_signer, *asset_id, &mediators, &auditors)?;
            println!("Updated keys of asset {asset_id} (issuer '{issuer_signer}')");
        }

        Commands::SetAssetFrozen {
            asset_id,
            freeze,
            unfreeze,
            signer,
            root,
        } => {
            if *freeze == *unfreeze {
                return Err(dart_testing_cli::ChainFailure::Internal(
                    "specify exactly one of --freeze/--unfreeze".into(),
                ));
            }
            if *root && signer.is_some() {
                return Err(dart_testing_cli::ChainFailure::Internal(
                    "--root cannot be combined with --signer".into(),
                ));
            }
            let caller = match (root, signer) {
                (true, None) => None,
                (false, Some(s)) => Some(s.as_str()),
                _ => {
                    return Err(dart_testing_cli::ChainFailure::Internal(
                        "use either --root or --signer".into(),
                    ));
                }
            };
            db.set_asset_frozen(caller, *asset_id, *freeze)?;
            println!(
                "Asset {asset_id} is now {}",
                if *freeze { "frozen" } else { "unfrozen" }
            );
        }

        Commands::RelayerFeePreview {
            signer_account,
            amount,
        } => {
            let (signer, account) = parse_signer_account(signer_account);
            let account = account.unwrap_or_else(|| "0".to_string());
            let nullifier = db.relayer_fee_preview(&signer, &account, *amount)?;
            println!("{}", hex::encode(nullifier.encode()));
        }

        Commands::RelayerBatchedProofs {
            signer_account,
            proofs,
            amount,
            broadcast,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = parse_signer_account(signer_account);
            let account = account.unwrap_or_else(|| "0".to_string());
            let fee_type_path = run_dir.join("relayer-payment.proof");
            if let Some(path) = read {
                let bytes = std::fs::read(path)?;
                let proof = dart_testing_cli::decode_exact::<
                    dart_testing_cli::FeePaymentWithBatchedProofs<dart_testing_cli::Limits>,
                >(&bytes, "relayer payment proof")?;
                db.relayer_batched_proofs_apply(rng, &signer, &account, &proof, *dry_run)?;
                println!(
                    "Relayer batch applied{} (fee {})",
                    if *dry_run { " (dry run)" } else { "" },
                    proof.fee_payment.amount
                );
            } else {
                let batch = build_batched_proofs(proofs)?;
                let amount = amount.ok_or_else(|| {
                    dart_testing_cli::ChainFailure::Internal(
                        "--amount is required when assembling".into(),
                    )
                })?;
                let batch_len = batch.len();
                if let Some(path) = write {
                    db.relayer_batched_proofs_new(
                        rng, &signer, &account, batch, amount, *broadcast, path,
                    )?;
                    println!("Wrote relayer payment for {batch_len} proofs");
                } else {
                    // assemble + apply in one shot
                    db.relayer_batched_proofs_new(
                        rng,
                        &signer,
                        &account,
                        batch,
                        amount,
                        *broadcast,
                        &fee_type_path,
                    )?;
                    let bytes = std::fs::read(&fee_type_path)?;
                    let proof = dart_testing_cli::decode_exact::<
                        dart_testing_cli::FeePaymentWithBatchedProofs<dart_testing_cli::Limits>,
                    >(&bytes, "relayer payment proof")?;
                    db.relayer_batched_proofs_apply(rng, &signer, &account, &proof, *dry_run)?;
                    println!("Relayer batch of {batch_len} proofs applied");
                }
            }
        }

        Commands::SubmitBatchedProofs {
            proofs,
            write,
            read,
            dry_run,
        } => {
            let batch: dart_testing_cli::BatchedProofs<dart_testing_cli::Limits> =
                if let Some(path) = read {
                    let bytes = std::fs::read(path)?;
                    dart_testing_cli::decode_exact(&bytes, "batched proofs")?
                } else {
                    build_batched_proofs(proofs)?
                };
            if let Some(path) = write {
                std::fs::write(path, batch.encode())?;
            }
            if read.is_some() || write.is_none() {
                db.submit_batched_proofs(rng, &batch, *dry_run)?;
                println!(
                    "Submitted batch of {} proofs{}",
                    batch.len(),
                    if *dry_run { " (dry run)" } else { "" }
                );
            } else {
                println!("Wrote batch of {} proofs", batch.len());
            }
        }

        Commands::CreateSettlement {
            venue_id,
            legs,
            hidden_asset_id,
            visibility,
            public_enc_keys,
            relayer_fee_nullifier,
            write,
            read,
            dry_run,
        } => {
            let leg_count = legs.len();
            let mut settlement_legs = Vec::new();
            for leg_str in legs {
                let parts: Vec<&str> = leg_str.split(':').collect();
                if parts.len() != 4 {
                    return Err(ChainFailure::Internal(
                        "Invalid leg format. Expected: sender_signer[-sender_account]:receiver_signer[-receiver_account]:asset_id:amount".into(),
                    ));
                }
                let asset_id: AssetId = parts[2]
                    .parse()
                    .map_err(|e| ChainFailure::Internal(format!("bad asset id: {e}")))?;
                let amount: Balance = parts[3]
                    .parse()
                    .map_err(|e| ChainFailure::Internal(format!("bad amount: {e}")))?;
                let (sender_signer, sender_account) =
                    resolve_signer_account(db, parts[0], Some(asset_id))?;
                let (receiver_signer, receiver_account) =
                    resolve_signer_account(db, parts[1], Some(asset_id))?;
                settlement_legs.push((
                    sender_signer,
                    sender_account,
                    receiver_signer,
                    receiver_account,
                    asset_id,
                    amount,
                ));
            }
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            let visibility = match visibility {
                Some(Visibility::Full) => dart_testing_cli::PartyVisibility::FullVisibility,
                Some(Visibility::None) => dart_testing_cli::PartyVisibility::NoVisibility,
                Some(Visibility::SenderSeesReceiver) => {
                    dart_testing_cli::PartyVisibility::OnlySenderSeesReceiver
                }
                Some(Visibility::ReceiverSeesSender) => {
                    dart_testing_cli::PartyVisibility::OnlyReceiverSeesSender
                }
                None => dart_testing_cli::PartyVisibility::FullVisibility,
            };
            let settlement_id = db.create_settlement_with_context(
                rng,
                venue_id,
                settlement_legs,
                !*hidden_asset_id,
                visibility,
                public_enc_keys,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!("Created settlement {settlement_id} with {leg_count} legs");
        }

        Commands::SenderAffirm {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            asset_id,
            amount,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(db, signer_account, *asset_id)?;
            check_leg_assertions(
                db,
                *settlement_id,
                *leg_index,
                *asset_id,
                *amount,
                LegRole::sender(),
                &signer,
                &account,
            )?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.sender_affirmation(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!(
                "Sender '{signer}:{account}' affirmed settlement {settlement_id} leg {leg_index}"
            );
        }

        Commands::ReceiverAffirm {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            asset_id,
            amount,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(db, signer_account, *asset_id)?;
            check_leg_assertions(
                db,
                *settlement_id,
                *leg_index,
                *asset_id,
                *amount,
                LegRole::receiver(),
                &signer,
                &account,
            )?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.receiver_affirmation(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!(
                "Receiver '{signer}:{account}' affirmed settlement {settlement_id} leg {leg_index}"
            );
        }

        Commands::MediatorAffirm {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            key_index,
            accept,
            reject,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = parse_signer_account(signer_account);
            let account = account.unwrap_or_else(|| "0".to_string());
            // `--reject` wins over the default accept; clap rejects both flags together.
            let accepted = *accept || !*reject;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.mediator_affirmation_with_context(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                *key_index,
                accepted,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!(
                "Mediator '{signer}:{account}' {} settlement {settlement_id} leg {leg_index}",
                if accepted { "accepted" } else { "rejected" }
            );
        }

        Commands::SenderCounterUpdate {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) =
                resolve_signer_account_by_settlement(db, signer_account, *settlement_id)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.sender_counter_update(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!("Sender '{signer}:{account}' updated counter for settlement {settlement_id} leg {leg_index}");
        }

        Commands::SenderRevertAffirmation {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) =
                resolve_signer_account_by_settlement(db, signer_account, *settlement_id)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.sender_revert_affirmation(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!("Sender '{signer}:{account}' reverted affirmation for settlement {settlement_id} leg {leg_index}");
        }

        Commands::ReceiverRevertAffirmation {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) =
                resolve_signer_account_by_settlement(db, signer_account, *settlement_id)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.receiver_revert_affirmation(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!("Receiver '{signer}:{account}' reverted affirmation for settlement {settlement_id} leg {leg_index}");
        }

        Commands::ReceiverClaim {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) =
                resolve_signer_account_by_settlement(db, signer_account, *settlement_id)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.receiver_claim(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!(
                "Receiver '{signer}:{account}' claimed settlement {settlement_id} leg {leg_index}"
            );
        }

        Commands::InstantSenderAffirmation {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) =
                resolve_signer_account_by_settlement(db, signer_account, *settlement_id)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.instant_sender_affirmation(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!("Sender '{signer}:{account}' instant-affirmed settlement {settlement_id} leg {leg_index}");
        }

        Commands::InstantReceiverAffirmation {
            signer_account,
            settlement_id,
            leg_index,
            relayer_fee_nullifier,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) =
                resolve_signer_account_by_settlement(db, signer_account, *settlement_id)?;
            let proof_action = ProofAction::new(write.clone(), read.clone(), *dry_run)?;
            db.instant_receiver_affirmation(
                rng,
                &signer,
                &account,
                *settlement_id,
                *leg_index,
                &decode_relayer_fee_ctx(&relayer_fee_nullifier)?,
                proof_action,
            )?;
            println!("Receiver '{signer}:{account}' instant-affirmed settlement {settlement_id} leg {leg_index}");
        }

        Commands::ListSigners => {
            let signers = db.store().list_identities()?;
            println!("Signers:");
            for (id, name) in signers {
                println!("  {name} (ID: {id})");
            }
        }

        Commands::ListAccounts { signer } => {
            let accounts = db.store().list_accounts(signer.as_deref())?;
            println!("DART Accounts:");
            for (signer_name, account) in accounts {
                println!("  {}:{} (ID: {})", signer_name, account.name, account.id);
            }
        }

        Commands::ListAssets => {
            let assets = db.store().list_assets()?;
            println!("Assets:");
            for (asset_id, details) in assets {
                println!(
                    "  Asset {asset_id} ({}, {} decimals, Total Supply: {})",
                    details.name, details.decimals, details.total_supply
                );
            }
        }

        Commands::ListFeeAccounts => {
            let pool = db.store().fee_pool_balance()?;
            let accounts = db.store().list_fee_accounts()?;
            println!("Fee pool balance: {pool}");
            println!("Fee accounts:");
            for (account, identity) in accounts {
                println!("  {account} (owner: {identity})");
            }
        }

        Commands::GetSettlement { settlement_id } => {
            let status = db.store().settlement_status(*settlement_id)?;
            println!("Settlement {settlement_id} status: {status}");
        }

        Commands::ShowLegs { settlement_id } => {
            let legs = db.store().show_legs(*settlement_id)?;
            println!("Settlement {settlement_id} legs:");
            for (leg_id, party, status) in legs {
                println!("  leg {leg_id}: {party} = {status}");
            }
        }

        Commands::ShowStorage => {
            let store = db.store();
            println!(
                "block {}  moment {}",
                store.block_number()?,
                store.timestamp()?
            );
            for tree in [TreeKind::Asset, TreeKind::Account, TreeKind::FeeAccount] {
                println!(
                    "{tree:?} tree: height={} next_leaf={} last_committed={}",
                    store.tree_height(tree)?,
                    store.next_leaf_index(tree)?,
                    store.last_committed_leaf_index(tree)?
                );
                let roots = store.list_root_blocks(tree)?;
                println!(
                    "  roots: {}",
                    roots
                        .iter()
                        .map(|b| b.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                );
            }
            println!("fee pool: {}", store.fee_pool_balance()?);
            println!("assets:");
            for (id, d) in store.list_assets()? {
                println!(
                    "  #{id} {} ({}) decimals={} supply={} frozen={:?}",
                    d.name,
                    d.symbol,
                    d.decimals,
                    d.total_supply,
                    store.asset_frozen(id)?
                );
            }
            println!("identities:");
            for (id, name) in store.list_identities()? {
                println!("  #{id} {name}");
            }
            println!("settlements:");
            for (id, status) in store.list_settlements()? {
                println!("  #{id} {status}");
            }
            println!("claims: {}", store.claim_count()?);
        }

        Commands::Trace => {
            let traces = db.store().read_trace()?;
            for trace in traces {
                println!(
                    "#{} block {} {} [{}]",
                    trace.id, trace.block, trace.call, trace.outcome
                );
                if let Some(err) = trace.error {
                    println!("  error: {err}");
                }
                for (event, detail) in trace.events {
                    println!("  event: {event} {detail}");
                }
            }
        }

        Commands::Replay { .. } => {
            return Err(dart_testing_cli::ChainFailure::Internal(
                "replay is handled before the chain is opened".into(),
            ));
        }
    }
    Ok(())
}

/// Decode `--relayer-fee-nullifier` into the batch submission ctx bound into party proofs.
fn decode_relayer_fee_ctx(spec: &Option<String>) -> dart_testing_cli::ChainResult<Vec<u8>> {
    match spec {
        None => Ok(vec![]),
        Some(hex_str) => {
            let bytes = hex::decode(hex_str).map_err(|e| {
                dart_testing_cli::ChainFailure::Internal(format!(
                    "bad --relayer-fee-nullifier hex: {e}"
                ))
            })?;
            let nullifier: polymesh_dart::FeeAccountStateNullifier =
                dart_testing_cli::decode_exact(&bytes, "relayer fee nullifier")?;
            Ok(polymesh_dart::relayer_batch_proof_context(&nullifier))
        }
    }
}

fn parse_signer_account(signer_account: &str) -> (String, Option<String>) {
    match signer_account.split_once('-') {
        Some((signer, account)) => (signer.to_string(), Some(account.to_string())),
        None => (signer_account.to_string(), None),
    }
}

/// Assemble a `BatchedProofs` from `type=path` proof-file specifiers (the proof files are
/// the same per-extrinsic files written by `-w`).
fn build_batched_proofs(
    specs: &[String],
) -> dart_testing_cli::ChainResult<dart_testing_cli::BatchedProofs<dart_testing_cli::Limits>> {
    use codec::DecodeWithMemTracking;
    use dart_testing_cli::{BatchedProof, ChainError, ChainFailure, ChainResult};

    fn decode<T: DecodeWithMemTracking>(path: &str) -> ChainResult<T> {
        let bytes = std::fs::read(path).map_err(ChainFailure::from)?;
        dart_testing_cli::decode_exact(&bytes, path)
    }

    let mut proofs = Vec::with_capacity(specs.len());
    for spec in specs {
        let (kind, path) = spec.split_once('=').ok_or_else(|| {
            ChainFailure::Internal(format!("proof spec '{spec}' must be type=path"))
        })?;
        let proof = match kind {
            "create-settlement" => BatchedProof::CreateSettlement(decode(path)?),
            "sender-affirm" => BatchedProof::SenderAffirmation(decode(path)?),
            "receiver-affirm" => BatchedProof::ReceiverAffirmation(decode(path)?),
            "mediator-affirm" => BatchedProof::MediatorAffirmation(decode(path)?, None),
            "sender-counter-update" => BatchedProof::SenderCounterUpdate(decode(path)?, None),
            "sender-revert" => BatchedProof::SenderRevertAffirmation(decode(path)?, None),
            "receiver-revert" => BatchedProof::ReceiverRevertAffirmation(decode(path)?, None),
            "receiver-claim" => BatchedProof::ReceiverClaim(decode(path)?, None),
            "instant-sender-affirm" => BatchedProof::InstantSenderAffirmation(decode(path)?, None),
            "instant-receiver-affirm" => {
                BatchedProof::InstantReceiverAffirmation(decode(path)?, None)
            }
            other => {
                return Err(ChainFailure::Internal(format!(
                    "unknown batched proof type '{other}'"
                )))
            }
        };
        proofs.push(proof);
    }
    let proofs = bounded_collections::BoundedVec::try_from(proofs)
        .map_err(|_| ChainFailure::Error(ChainError::TooManyProofs))?;
    Ok(dart_testing_cli::BatchedProofs { proofs })
}

/// Parse `-f signer-account:amount` fee-account specifiers.
fn parse_fee_accounts(
    fee_accounts: &[String],
) -> dart_testing_cli::ChainResult<Vec<(String, String, polymesh_dart::Balance)>> {
    fee_accounts
        .iter()
        .map(|spec| {
            let (signer_account, amount) = spec.rsplit_once(':').ok_or_else(|| {
                dart_testing_cli::ChainFailure::Internal(format!(
                    "fee account '{spec}' must be in signer-account:amount format"
                ))
            })?;
            let amount = amount.parse().map_err(|_| {
                dart_testing_cli::ChainFailure::Internal(format!("invalid fee amount in '{spec}'"))
            })?;
            let (signer, account) = parse_signer_account(signer_account);
            let account = account.unwrap_or_else(|| "0".to_string());
            Ok((signer, account, amount))
        })
        .collect()
}

/// Validate the optional `--asset`/`--amount` assertions against the encrypted leg.
fn check_leg_assertions(
    db: &Chain,
    settlement_id: SettlementId,
    leg_index: LegId,
    asset_id: Option<AssetId>,
    amount: Option<Balance>,
    role: LegRole,
    signer: &str,
    account: &str,
) -> ChainResult<()> {
    if asset_id.is_none() && amount.is_none() {
        return Ok(());
    }
    let keys = db.find_account(signer, account)?.account_keys()?;
    let leg = db.preview_leg(settlement_id, leg_index, role, &keys)?;
    if let Some(expected) = asset_id {
        if leg.asset_id() != expected {
            return Err(ChainFailure::Internal(format!(
                "settlement {settlement_id} leg {leg_index} carries asset {}, expected {expected}",
                leg.asset_id()
            )));
        }
    }
    if let Some(expected) = amount {
        if leg.amount() != expected {
            return Err(ChainFailure::Internal(format!(
                "settlement {settlement_id} leg {leg_index} carries amount {}, expected {expected}",
                leg.amount()
            )));
        }
    }
    Ok(())
}

fn resolve_signer_account(
    db: &Chain,
    signer_account: &str,
    asset_id: Option<AssetId>,
) -> ChainResult<(String, String)> {
    let (signer, account_opt) = parse_signer_account(signer_account);
    let account = match account_opt {
        Some(account) => account,
        None => {
            let asset_id = asset_id.ok_or_else(|| {
                ChainFailure::Internal(
                    "Account name is required when asset_id is not provided".into(),
                )
            })?;
            db.find_account_by_asset(&signer, asset_id)?.name
        }
    };
    Ok((signer, account))
}

/// Resolve the account for a settlement command. The asset is not always named on the command
/// line, so fall back to the signer's unique account (account "0" by convention when unambiguous).
fn resolve_signer_account_by_settlement(
    db: &Chain,
    signer_account: &str,
    _settlement_id: SettlementId,
) -> ChainResult<(String, String)> {
    let (signer, account_opt) = parse_signer_account(signer_account);
    let account = match account_opt {
        Some(account) => account,
        None => {
            let accounts = db.store().list_accounts(Some(&signer))?;
            if accounts.len() == 1 {
                accounts[0].1.name.clone()
            } else {
                "0".to_string()
            }
        }
    };
    Ok((signer, account))
}
