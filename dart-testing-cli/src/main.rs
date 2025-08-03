use std::path::PathBuf;

use anyhow::Result;
use clap::{Parser, Subcommand};
use dart_testing_cli::*;
use polymesh_dart::*;
use rand::thread_rng;

#[derive(Parser)]
#[command(name = "dart-testing-cli")]
#[command(about = "A CLI tool for testing DART operations with SQLite backend")]
struct Cli {
    /// Path to the SQLite database file
    #[arg(short, long, default_value = "dart_test.db")]
    database: String,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Initialize/reset the SQLite database
    Init,

    /// Create a new signer
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

    /// Create a new asset
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
    },

    /// End the current block (record tree roots)
    EndBlock,

    /// Register a DART account with an asset
    RegisterAccount {
        /// Signer and account in format signer-account (account optional, will find by asset_id)
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

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Mint assets (only asset issuer can do this)
    MintAssets {
        /// Issuer signer and account in format signer-account (account optional, will find by asset_id)
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

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Create a settlement with legs
    CreateSettlement {
        /// Venue ID for the settlement
        #[arg(short, long)]
        venue_id: String,
        /// Settlement legs in format: sender_signer[-sender_account]:receiver_signer[-receiver_account]:asset_id:amount
        #[arg(short, long = "leg")]
        legs: Vec<String>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Affirm a settlement leg as sender
    SenderAffirm {
        /// Signer and account in format signer-account (account optional, will find by asset_id)
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(long = "settlement")]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Asset ID
        #[arg(short, long = "asset")]
        asset_id: AssetId,
        /// Amount
        #[arg(short = 'm', long)]
        amount: Balance,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Affirm a settlement leg as receiver
    ReceiverAffirm {
        /// Signer and account in format signer-account (account optional, will find by asset_id)
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(long = "settlement")]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Asset ID
        #[arg(short, long = "asset")]
        asset_id: AssetId,
        /// Amount
        #[arg(short = 'm', long)]
        amount: Balance,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Affirm a settlement leg as mediator
    MediatorAffirm {
        /// Signer and account in format signer-account (account optional, will find by asset_id)
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(long = "settlement")]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Accept or reject the settlement
        #[arg(short, long, action)]
        accept: bool,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Claim assets as receiver
    ReceiverClaim {
        /// Signer and account in format signer-account (account optional, will find by asset_id)
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(long = "settlement")]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Asset ID (optional, will be used to help find the account)
        #[arg(short, long = "asset")]
        asset_id: Option<AssetId>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Update sender counter for executed settlement
    SenderCounterUpdate {
        /// Signer and account in format signer-account (account optional, will find by asset_id)
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(long = "settlement")]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Asset ID (optional, will be used to help find the account)
        #[arg(short, long = "asset")]
        asset_id: Option<AssetId>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,

        /// Dry run without applying changes
        #[arg(long = "dry-run")]
        dry_run: bool,
    },

    /// Reverse sender affirmation for rejected settlement
    SenderReversal {
        /// Signer and account in format signer-account (account optional, will find by asset_id)
        #[arg(short, long)]
        signer_account: String,
        /// Settlement ID
        #[arg(long = "settlement")]
        settlement_id: SettlementId,
        /// Leg index
        #[arg(short, long = "leg")]
        leg_index: LegId,
        /// Asset ID (optional, will be used to help find the account)
        #[arg(short, long = "asset")]
        asset_id: Option<AssetId>,
        /// Write proof to file instead of applying
        #[arg(short, long)]
        write: Option<PathBuf>,
        /// Read proof from file and apply
        #[arg(short, long)]
        read: Option<PathBuf>,

        /// Dry run without applying changes
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

    /// Get settlement status
    GetSettlement {
        /// Settlement ID
        #[arg(short, long)]
        settlement_id: SettlementId,
    },
}

#[derive(clap::ValueEnum, Clone)]
enum AuditorType {
    Auditor,
    Mediator,
}

fn main() -> Result<()> {
    env_logger::init();

    let cli = Cli::parse();
    let mut db = DartTestingDb::new(&cli.database)?;
    let mut rng = thread_rng();

    match cli.command {
        Commands::Init => {
            db.initialize_db()?;
            println!("Database initialized successfully");
        }

        Commands::CreateSigner { name } => {
            let signer = db.create_signer(&name)?;
            println!("Created signer: {} (ID: {})", signer.name, signer.id);
        }

        Commands::CreateAccount { signer_account } => {
            let (signer, account) = parse_signer_account(&signer_account);
            let account_name = account
                .ok_or_else(|| anyhow::anyhow!("Account name is required for CreateAccount"))?;

            let account_info = db.create_dart_account(&mut rng, &signer, &account_name)?;
            println!(
                "Created account '{}' for signer '{}' (ID: {})",
                account_info.name, signer, account_info.id
            );
        }

        Commands::CreateAsset {
            signer,
            auditor_type,
            auditor_signer_account,
        } => {
            let (auditor_signer, auditor_account) = parse_signer_account(&auditor_signer_account);
            let auditor_account = auditor_account.unwrap_or_else(|| "0".to_string());

            let auditor_account_info = db.get_dart_account(&auditor_signer, &auditor_account)?;
            let auditor_keys = db.get_account_public_keys(&auditor_account_info)?;

            let auditor = match auditor_type {
                AuditorType::Auditor => AuditorOrMediator::auditor(&auditor_keys.enc),
                AuditorType::Mediator => AuditorOrMediator::mediator(&auditor_keys),
            };

            let asset = db.create_asset(&signer, auditor)?;
            println!(
                "Created asset {} with issuer '{}' and {} '{}:{}'",
                asset.asset_id,
                signer,
                match auditor_type {
                    AuditorType::Auditor => "auditor",
                    AuditorType::Mediator => "mediator",
                },
                auditor_signer,
                auditor_account
            );
        }

        Commands::EndBlock => {
            db.end_block()?;
            println!("Block ended and tree roots recorded");
        }

        Commands::RegisterAccount {
            signer_account,
            asset_id,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(&db, &signer_account, Some(asset_id))?;

            let proof_action = ProofAction::new(write, read, dry_run)?;

            db.register_account_with_asset(&mut rng, &signer, &account, asset_id, proof_action)?;
            println!(
                "Registered account '{}:{}' with asset {}",
                signer, account, asset_id
            );
        }

        Commands::MintAssets {
            signer_account,
            asset_id,
            amount,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(&db, &signer_account, Some(asset_id))?;

            let proof_action = ProofAction::new(write, read, dry_run)?;

            db.mint_assets(&mut rng, &signer, &account, asset_id, amount, proof_action)?;
            println!(
                "Minted {} units of asset {} for account '{}:{}'",
                amount, asset_id, signer, account
            );
        }

        Commands::CreateSettlement {
            venue_id,
            legs,
            write,
            read,
            dry_run,
        } => {
            let leg_count = legs.len();
            let mut settlement_legs = Vec::new();

            let mut proof_action = ProofAction::new(write, read, dry_run)?;

            for leg_str in legs {
                let parts: Vec<&str> = leg_str.split(':').collect();
                if parts.len() != 4 {
                    return Err(anyhow::anyhow!("Invalid leg format. Expected: sender_signer[-sender_account]:receiver_signer[-receiver_account]:asset_id:amount"));
                }

                let sender_signer_account = parts[0];
                let receiver_signer_account = parts[1];
                let asset_id: AssetId = parts[2].parse()?;
                let amount: Balance = parts[3].parse()?;

                // Parse sender
                let (sender_signer, sender_account) =
                    resolve_signer_account(&db, sender_signer_account, Some(asset_id))?;

                // Parse receiver
                let (receiver_signer, receiver_account) =
                    resolve_signer_account(&db, receiver_signer_account, Some(asset_id))?;

                settlement_legs.push((
                    sender_signer,
                    sender_account,
                    receiver_signer,
                    receiver_account,
                    asset_id,
                    amount,
                ));
            }

            let proof = if let Some(proof) = proof_action.get_proof()? {
                proof
            } else {
                db.create_settlement_gen_proof(&mut rng, &venue_id, settlement_legs)?
            };

            if proof_action.apply_proof() {
                let settlement_id = db.create_settlement_verify_proof(&mut rng, proof)?;
                println!(
                    "Created settlement {} with {} legs",
                    settlement_id, leg_count
                );
            } else {
                // If proof action is to generate only, save proof and return
                proof_action.save_proof(&proof)?;
                println!("Created settlement proof with {} legs", leg_count);
                return Ok(());
            }
        }

        Commands::SenderAffirm {
            signer_account,
            settlement_id,
            leg_index,
            asset_id,
            amount,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(&db, &signer_account, Some(asset_id))?;

            let proof_action = ProofAction::new(write, read, dry_run)?;

            db.sender_affirmation(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                asset_id,
                amount,
                proof_action,
            )?;
            println!(
                "Sender '{}:{}' affirmed settlement {} leg {}",
                signer, account, settlement_id, leg_index
            );
        }

        Commands::ReceiverAffirm {
            signer_account,
            settlement_id,
            leg_index,
            asset_id,
            amount,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(&db, &signer_account, Some(asset_id))?;

            let proof_action = ProofAction::new(write, read, dry_run)?;

            db.receiver_affirmation(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                asset_id,
                amount,
                proof_action,
            )?;
            println!(
                "Receiver '{}:{}' affirmed settlement {} leg {}",
                signer, account, settlement_id, leg_index
            );
        }

        Commands::MediatorAffirm {
            signer_account,
            settlement_id,
            leg_index,
            accept,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = parse_signer_account(&signer_account);

            let proof_action = ProofAction::new(write, read, dry_run)?;

            let account = account.unwrap_or_else(|| "0".to_string());
            db.mediator_affirmation(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                accept,
                proof_action,
            )?;
            println!(
                "Mediator '{}:{}' {} settlement {} leg {}",
                signer,
                account,
                if accept { "accepted" } else { "rejected" },
                settlement_id,
                leg_index
            );
        }

        Commands::ReceiverClaim {
            signer_account,
            settlement_id,
            leg_index,
            asset_id,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(&db, &signer_account, asset_id)?;

            let proof_action = ProofAction::new(write, read, dry_run)?;

            db.receiver_claim(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                proof_action,
            )?;
            println!(
                "Receiver '{}:{}' claimed settlement {} leg {}",
                signer, account, settlement_id, leg_index
            );
        }

        Commands::SenderCounterUpdate {
            signer_account,
            settlement_id,
            leg_index,
            asset_id,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(&db, &signer_account, asset_id)?;

            let proof_action = ProofAction::new(write, read, dry_run)?;

            db.sender_counter_update(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                proof_action,
            )?;
            println!(
                "Sender '{}:{}' updated counter for settlement {} leg {}",
                signer, account, settlement_id, leg_index
            );
        }

        Commands::SenderReversal {
            signer_account,
            settlement_id,
            leg_index,
            asset_id,
            write,
            read,
            dry_run,
        } => {
            let (signer, account) = resolve_signer_account(&db, &signer_account, asset_id)?;

            let proof_action = ProofAction::new(write, read, dry_run)?;

            db.sender_reversal(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                proof_action,
            )?;
            println!(
                "Sender '{}:{}' reversed affirmation for settlement {} leg {}",
                signer, account, settlement_id, leg_index
            );
        }

        Commands::ListSigners => {
            let signers = db.list_signers()?;
            println!("Signers:");
            for signer in signers {
                println!("  {} (ID: {})", signer.name, signer.id);
            }
        }

        Commands::ListAccounts { signer } => {
            let accounts = db.list_dart_accounts(signer.as_deref())?;
            println!("DART Accounts:");
            for (signer_name, account) in accounts {
                println!("  {}:{} (ID: {})", signer_name, account.name, account.id);
            }
        }

        Commands::ListAssets => {
            let assets = db.list_assets()?;
            println!("Assets:");
            for asset in assets {
                println!(
                    "  Asset {} (Total Supply: {})",
                    asset.asset_id, asset.total_supply
                );
            }
        }

        Commands::GetSettlement { settlement_id } => {
            let status = db.get_settlement_status(settlement_id)?;
            println!("Settlement {} status: {}", settlement_id, status);
        }
    }

    Ok(())
}

fn parse_signer_account(signer_account: &str) -> (String, Option<String>) {
    match signer_account.split_once('-') {
        Some((signer, account)) => (signer.to_string(), Some(account.to_string())),
        None => (signer_account.to_string(), None),
    }
}

fn find_account_by_asset(
    db: &DartTestingDb,
    signer_name: &str,
    asset_id: AssetId,
) -> Result<String> {
    let accounts = db.list_dart_accounts(Some(signer_name))?;

    for (_, account_info) in accounts {
        // Check if this account is registered with the asset
        if let Ok(_) = db.get_account_asset_state(&account_info, asset_id) {
            return Ok(account_info.name);
        }
    }

    Err(anyhow::anyhow!(
        "No account found for signer '{}' registered with asset {}",
        signer_name,
        asset_id
    ))
}

fn resolve_signer_account(
    db: &DartTestingDb,
    signer_account: &str,
    asset_id: Option<AssetId>,
) -> Result<(String, String)> {
    let (signer, account_opt) = parse_signer_account(signer_account);

    let account = match account_opt {
        Some(account) => account,
        None => {
            let asset_id = asset_id.ok_or_else(|| {
                anyhow::anyhow!("Account name is required when asset_id is not provided")
            })?;
            find_account_by_asset(db, &signer, asset_id)?
        }
    };

    Ok((signer, account))
}
