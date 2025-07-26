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
        name: String,
    },

    /// Create a new DART account for a signer
    CreateAccount {
        /// Name of the signer who owns the account
        signer: String,
        /// Name of the account
        account: String,
    },

    /// Create a new asset
    CreateAsset {
        /// Name of the issuer signer
        issuer: String,
        /// Type of auditor/mediator (auditor or mediator)
        #[arg(value_enum)]
        auditor_type: AuditorType,
        /// Signer name for the auditor/mediator
        auditor_signer: String,
        /// Account name for the auditor/mediator
        auditor_account: String,
    },

    /// End the current block (record tree roots)
    EndBlock,

    /// Register a DART account with an asset
    RegisterAccount {
        /// Signer name
        signer: String,
        /// Account name
        account: String,
        /// Asset ID
        asset_id: AssetId,
    },

    /// Mint assets (only asset issuer can do this)
    MintAssets {
        /// Issuer signer name
        issuer: String,
        /// Account name
        account: String,
        /// Asset ID
        asset_id: AssetId,
        /// Amount to mint
        amount: Balance,
    },

    /// Create a settlement with legs
    CreateSettlement {
        /// Venue ID for the settlement
        venue_id: String,
        /// Settlement legs in format: sender_signer:sender_account:receiver_signer:receiver_account:asset_id:amount
        legs: Vec<String>,
    },

    /// Affirm a settlement leg as sender
    SenderAffirm {
        /// Signer name
        signer: String,
        /// Account name
        account: String,
        /// Settlement ID
        settlement_id: SettlementId,
        /// Leg index
        leg_index: LegId,
        /// Asset ID
        asset_id: AssetId,
        /// Amount
        amount: Balance,
    },

    /// Affirm a settlement leg as receiver
    ReceiverAffirm {
        /// Signer name
        signer: String,
        /// Account name
        account: String,
        /// Settlement ID
        settlement_id: SettlementId,
        /// Leg index
        leg_index: LegId,
        /// Asset ID
        asset_id: AssetId,
        /// Amount
        amount: Balance,
    },

    /// Affirm a settlement leg as mediator
    MediatorAffirm {
        /// Signer name
        signer: String,
        /// Account name
        account: String,
        /// Settlement ID
        settlement_id: SettlementId,
        /// Leg index
        leg_index: LegId,
        /// Accept or reject the settlement
        #[arg(short, long, action)]
        accept: bool,
    },

    /// Claim assets as receiver
    ReceiverClaim {
        /// Signer name
        signer: String,
        /// Account name
        account: String,
        /// Settlement ID
        settlement_id: SettlementId,
        /// Leg index
        leg_index: LegId,
    },

    /// List all signers
    ListSigners,

    /// List DART accounts
    ListAccounts {
        /// Optional signer name to filter by
        signer: Option<String>,
    },

    /// List assets
    ListAssets,

    /// Get settlement status
    GetSettlement {
        /// Settlement ID
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

        Commands::CreateAccount { signer, account } => {
            let account_info = db.create_dart_account(&mut rng, &signer, &account)?;
            println!(
                "Created account '{}' for signer '{}' (ID: {})",
                account_info.name, signer, account_info.id
            );
        }

        Commands::CreateAsset {
            issuer,
            auditor_type,
            auditor_signer,
            auditor_account,
        } => {
            let auditor_account_info = db.get_dart_account(&auditor_signer, &auditor_account)?;
            let auditor_keys = db.get_account_public_keys(&auditor_account_info)?;

            let auditor = match auditor_type {
                AuditorType::Auditor => AuditorOrMediator::auditor(&auditor_keys.enc),
                AuditorType::Mediator => AuditorOrMediator::mediator(&auditor_keys),
            };

            let asset = db.create_asset(&issuer, auditor)?;
            println!(
                "Created asset {} with issuer '{}' and {} '{}'",
                asset.asset_id,
                issuer,
                match auditor_type {
                    AuditorType::Auditor => "auditor",
                    AuditorType::Mediator => "mediator",
                },
                auditor_signer
            );
        }

        Commands::EndBlock => {
            db.end_block()?;
            println!("Block ended and tree roots recorded");
        }

        Commands::RegisterAccount {
            signer,
            account,
            asset_id,
        } => {
            db.register_account_with_asset(&mut rng, &signer, &account, asset_id)?;
            println!(
                "Registered account '{}:{}' with asset {}",
                signer, account, asset_id
            );
        }

        Commands::MintAssets {
            issuer,
            account,
            asset_id,
            amount,
        } => {
            db.mint_assets(&mut rng, &issuer, &account, asset_id, amount)?;
            println!(
                "Minted {} units of asset {} for issuer '{}:{}'",
                amount, asset_id, issuer, account,
            );
        }

        Commands::CreateSettlement { venue_id, legs } => {
            let leg_count = legs.len();
            let mut settlement_legs = Vec::new();

            for leg_str in legs {
                let parts: Vec<&str> = leg_str.split(':').collect();
                if parts.len() != 6 {
                    return Err(anyhow::anyhow!("Invalid leg format. Expected: sender_signer:sender_account:receiver_signer:receiver_account:asset_id:amount"));
                }

                let sender_signer = parts[0].to_string();
                let sender_account = parts[1].to_string();
                let receiver_signer = parts[2].to_string();
                let receiver_account = parts[3].to_string();
                let asset_id = parts[4].parse()?;
                let amount = parts[5].parse()?;

                settlement_legs.push((
                    sender_signer,
                    sender_account,
                    receiver_signer,
                    receiver_account,
                    asset_id,
                    amount,
                ));
            }

            let settlement_id = db.create_settlement(&mut rng, &venue_id, settlement_legs)?;
            println!(
                "Created settlement {} with {} legs",
                settlement_id, leg_count
            );
        }

        Commands::SenderAffirm {
            signer,
            account,
            settlement_id,
            leg_index,
            asset_id,
            amount,
        } => {
            db.sender_affirmation(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                asset_id,
                amount,
            )?;
            println!(
                "Sender '{}:{}' affirmed settlement {} leg {}",
                signer, account, settlement_id, leg_index
            );
        }

        Commands::ReceiverAffirm {
            signer,
            account,
            settlement_id,
            leg_index,
            asset_id,
            amount,
        } => {
            db.receiver_affirmation(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                asset_id,
                amount,
            )?;
            println!(
                "Receiver '{}:{}' affirmed settlement {} leg {}",
                signer, account, settlement_id, leg_index
            );
        }

        Commands::MediatorAffirm {
            signer,
            account,
            settlement_id,
            leg_index,
            accept,
        } => {
            db.mediator_affirmation(
                &mut rng,
                &signer,
                &account,
                settlement_id,
                leg_index,
                accept,
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
            signer,
            account,
            settlement_id,
            leg_index,
        } => {
            db.receiver_claim(&mut rng, &signer, &account, settlement_id, leg_index)?;
            println!(
                "Receiver '{}:{}' claimed settlement {} leg {}",
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
