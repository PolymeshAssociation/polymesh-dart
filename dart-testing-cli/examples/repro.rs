//! Scratch repro: settlement with reveal_asset_id toggle + sender/receiver affirm.
use dart_testing_cli::*;
use rand::thread_rng;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-repro");
    let _ = std::fs::remove_dir_all(dir);
    std::fs::create_dir_all(dir)?;
    let db = dir.join("chain.db");
    let chain = Chain::open(&db, TestConfig::default())?;
    chain.initialize()?;
    let base = &mut thread_rng();
    let rng = &mut polymesh_dart_bp::util::reseed_rng(base);

    for name in ["issuer1", "investor", "mediator", "auditor"] {
        chain.create_signer(name)?;
    }
    for (signer, account) in [
        ("issuer1", "0"),
        ("investor", "0"),
        ("mediator", "0"),
        ("auditor", "0"),
    ] {
        chain.create_account(rng, signer, account)?;
        chain.register_accounts(
            rng,
            signer,
            account,
            ProofAction::GenerateAndApply { dry_run: false },
        )?;
    }

    let auditor_keys = chain
        .find_account("auditor", "0")?
        .account_keys()?
        .public_keys();
    let mediator_keys = chain
        .find_account("mediator", "0")?
        .account_keys()?
        .public_keys();
    let asset = chain.create_asset(
        "issuer1",
        "a1",
        "A1",
        6,
        &[],
        &[(mediator_keys.acct, mediator_keys.enc)],
        &[auditor_keys.enc],
    )?;
    for signer in ["issuer1", "investor"] {
        chain.register_account_assets(
            rng,
            signer,
            "0",
            asset,
            ProofAction::GenerateAndApply { dry_run: false },
        )?;
    }
    chain.end_block()?;
    chain.mint_assets(
        rng,
        "issuer1",
        "0",
        asset,
        1000,
        ProofAction::GenerateAndApply { dry_run: false },
    )?;
    chain.end_block()?;

    // Settlement with reveal_asset_id: true (as the CLI builds it).
    let reveal = !std::env::args().any(|a| a == "--hidden");
    let mut leg_builders = Vec::new();
    for (s, sa, r, ra, asset_id, amount) in [(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        500u64,
    )] {
        leg_builders.push(LegBuilder {
            sender: chain.find_account(&s, &sa)?.account_keys()?.public_keys(),
            receiver: chain.find_account(&r, &ra)?.account_keys()?.public_keys(),
            asset: chain.asset_state_pub(asset_id)?,
            amount,
            config: LegConfig {
                reveal_asset_id: reveal,
                ..Default::default()
            },
            public_enc_keys: vec![],
        });
    }
    let mut builder = SettlementBuilder::<dart_testing_cli::Limits>::new(b"repro");
    for leg in leg_builders {
        builder = builder.leg(leg);
    }
    let settlement = builder.encrypt_and_prove(rng, &chain.asset_tree)?;
    let settlement_id = chain.create_settlement_verify_pub(rng, &settlement)?;
    println!("settlement {settlement_id} (reveal_asset_id={reveal} )");

    chain.sender_affirmation(
        rng,
        "issuer1",
        "0",
        settlement_id,
        0,
        &[],
        ProofAction::GenerateAndApply { dry_run: false },
    )?;
    println!("sender affirm OK");

    if std::env::args().any(|a| a == "--endbetween") {
        chain.end_block()?;
    }

    chain.receiver_affirmation(
        rng,
        "investor",
        "0",
        settlement_id,
        0,
        &[],
        ProofAction::GenerateAndApply { dry_run: false },
    )?;
    println!("receiver affirm OK");

    // status checks
    let s = chain.store().settlement_status(settlement_id)?;
    println!("status after sender+receiver: {s}");
    Ok(())
}
