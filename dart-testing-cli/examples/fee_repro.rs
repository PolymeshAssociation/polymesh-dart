//! Debug repro: in-process fee registration + topup path lookup.
//!
//! Run with: cargo run -p dart-testing-cli --release --example fee_repro

use codec::Encode;
use dart_testing_cli::*;
use polymesh_dart_bp::util::reseed_rng;
use rand::thread_rng;

fn main() -> dart_testing_cli::ChainResult<()> {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-fee-repro");
    std::fs::create_dir_all(dir).unwrap();
    let db = dir.join("dart_test.db");
    let _ = std::fs::remove_file(&db);
    let chain = Chain::open(&db, TestConfig::default()).unwrap();
    chain.initialize().unwrap();
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    for name in ["issuer1", "investor"] {
        chain.create_signer(name).unwrap();
    }
    for signer in ["issuer1", "investor"] {
        chain.create_account(rng, signer, "0").unwrap();
        chain
            .register_accounts(
                rng,
                signer,
                "0",
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }

    let keys = chain
        .find_account("issuer1", "0")
        .unwrap()
        .account_keys()
        .unwrap();

    // Register the fee account (generate + apply in one shot).
    chain
        .register_fee_accounts(
            rng,
            "issuer1",
            &[("issuer1".to_string(), "0".to_string(), 100)],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    println!(
        "registered; fee leaves = {}",
        chain.store().next_leaf_index(TreeKind::FeeAccount).unwrap()
    );

    // Dump the stored leaf bytes and the prover state commitment.
    let stored = chain
        .store()
        .get_leaf(TreeKind::FeeAccount, 0)
        .unwrap()
        .unwrap();
    println!("stored leaf : {}", hex::encode(&stored));

    let state = chain
        .store()
        .prover_fee_account_state(&keys.acct.public, polymesh_dart::FEE_ASSET_ID)
        .unwrap()
        .unwrap();
    let commitment = state.current_commitment().unwrap();
    let leaf = commitment.as_leaf_value().unwrap();
    println!("state leaf  : {}", hex::encode(&leaf.encode()));

    chain.end_block().unwrap();

    // Now attempt a topup generation.
    let res = chain.topup_fee_accounts(
        rng,
        "issuer1",
        &[("issuer1".to_string(), "0".to_string(), 200)],
        ProofAction::GenerateAndApply { dry_run: false },
    );
    println!("topup result: {res:?}");
    Ok(())
}
