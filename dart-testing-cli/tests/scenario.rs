//! P0 scenario test: the full DART settlement flow through the simulated pallet.
//!
//! Mirrors `reinit_db_and_run_testing.sh` in-process (fast: proofs run once) and asserts the
//! pallet-equivalent settlement state machine (counters, tombstone, revert-while-pending).

use dart_testing_cli::*;
use polymesh_dart_bp::util::reseed_rng;
use rand::thread_rng;
use rand_core::{CryptoRng, RngCore};

fn setup(dir: &std::path::Path) -> Chain {
    std::fs::create_dir_all(dir).unwrap();
    let db = dir.join("dart_test.db");
    let _ = std::fs::remove_file(&db);
    let config = TestConfig::default();
    let chain = Chain::open(&db, config).unwrap();
    chain.initialize().unwrap();
    chain
}

fn ids(chain: &Chain, rng: &mut (impl RngCore + CryptoRng)) {
    for name in ["issuer1", "issuer2", "investor", "mediator", "auditor"] {
        chain.create_signer(name).unwrap();
    }
    for (signer, account) in [
        ("issuer1", "0"),
        ("issuer2", "0"),
        ("investor", "0"),
        ("mediator", "0"),
        ("auditor", "0"),
    ] {
        chain.create_account(rng, signer, account).unwrap();
        chain
            .register_accounts(
                rng,
                signer,
                account,
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }
}

#[test]
fn settlement_flow_and_state_machine() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-main");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);

    // auditor-only asset 0, mediator asset 1.
    let auditor_keys = chain
        .find_account("auditor", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    chain
        .create_asset("issuer1", "a0", "A0", 6, &[], &[], &[auditor_keys.enc])
        .unwrap();
    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "a1",
            "A1",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    assert_eq!(asset, 1);

    for signer in ["issuer1", "issuer2", "investor"] {
        chain
            .register_account_assets(
                rng,
                signer,
                "0",
                asset,
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }
    chain.end_block().unwrap();

    chain
        .mint_assets(
            rng,
            "issuer1",
            "0",
            asset,
            1000,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();

    // ---- settlement 1: rejected by the mediator, then both parties revert (finalizes).
    chain
        .create_settlement(
            rng,
            "test_reject",
            vec![(
                "issuer1".into(),
                "0".into(),
                "investor".into(),
                "0".into(),
                asset,
                500u64,
            )],
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    let s1 = 1;

    chain
        .sender_affirmation(
            rng,
            "issuer1",
            "0",
            s1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    // The receiver affirmation binds the sender's affirmed leaf (ct_s'), so it must be built
    // against a root that includes the sender's leaf: end the block first.
    chain.end_block().unwrap();
    chain
        .receiver_affirmation(
            rng,
            "investor",
            "0",
            s1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    assert_eq!(chain.store().settlement_status(s1).unwrap(), "Pending");

    chain.end_block().unwrap();
    chain
        .mediator_affirmation(
            rng,
            "mediator",
            "0",
            s1,
            0,
            0,
            false,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    assert_eq!(chain.store().settlement_status(s1).unwrap(), "Rejected");

    chain
        .receiver_revert_affirmation(
            rng,
            "investor",
            "0",
            s1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    // One party finalized, settlement stays Rejected.
    assert_eq!(chain.store().settlement_status(s1).unwrap(), "Rejected");
    // The sender revert binds the receiver's reverted leaf: end the block first.
    chain.end_block().unwrap();
    chain
        .sender_revert_affirmation(
            rng,
            "issuer1",
            "0",
            s1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    // Both non-mediator parties finalized -> Rejected settlement finalizes (pallet semantics).
    assert_eq!(chain.store().settlement_status(s1).unwrap(), "Finalized");

    // Replay guard: creating the same settlement again (same proof bytes via file) is rejected.
    chain.end_block().unwrap();

    // ---- settlement 2: mediator affirms; claim + counter update finalize it.
    chain
        .create_settlement(
            rng,
            "test_accept",
            vec![(
                "issuer1".into(),
                "0".into(),
                "investor".into(),
                "0".into(),
                asset,
                500u64,
            )],
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    let s2 = 2;
    chain
        .sender_affirmation(
            rng,
            "issuer1",
            "0",
            s2,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();
    chain
        .receiver_affirmation(
            rng,
            "investor",
            "0",
            s2,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();
    chain
        .mediator_affirmation(
            rng,
            "mediator",
            "0",
            s2,
            0,
            0,
            true,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    assert_eq!(chain.store().settlement_status(s2).unwrap(), "Executed");

    chain
        .receiver_claim(
            rng,
            "investor",
            "0",
            s2,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    // The counter-update proof binds the receiver's claimed leaf: end the block first.
    chain.end_block().unwrap();
    chain
        .sender_counter_update(
            rng,
            "issuer1",
            "0",
            s2,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    // With the mediator affirmed, the settlement finalizes once both non-mediator parties finalize.
    assert_eq!(chain.store().settlement_status(s2).unwrap(), "Finalized");

    // Balances: investor 500, issuer1 500.
    let investor = chain.find_account("investor", "0").unwrap();
    let investor_state = chain
        .store()
        .prover_account_state(&investor.public_keys.acct, asset)
        .unwrap()
        .unwrap();
    assert_eq!(investor_state.current_state.balance, 500);
    let issuer = chain.find_account("issuer1", "0").unwrap();
    let issuer_state = chain
        .store()
        .prover_account_state(&issuer.public_keys.acct, asset)
        .unwrap()
        .unwrap();
    assert_eq!(issuer_state.current_state.balance, 500);

    // ---- settlement 3: instant affirmations (NotLastPendingAffirmation + last-pending path).
    chain.end_block().unwrap();
    chain
        .create_settlement(
            rng,
            "test_instant",
            vec![(
                "issuer1".into(),
                "0".into(),
                "investor".into(),
                "0".into(),
                asset,
                100u64,
            )],
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    let s3 = 3;
    chain
        .sender_affirmation(
            rng,
            "issuer1",
            "0",
            s3,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    // Not the last pending affirmation (mediator + receiver remain).
    let err = chain
        .instant_receiver_affirmation(
            rng,
            "investor",
            "0",
            s3,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap_err();
    assert_eq!(err.name(), "NotLastPendingAffirmation");
    // The failed dispatch must not have mutated party statuses.
    let statuses = chain
        .store()
        .leg_statuses(&chain.store().resolve_settlement_alias(s3).unwrap())
        .unwrap();
    assert_eq!(
        statuses,
        vec![
            (0, "Mediator(0)".into(), "Pending".into()),
            (0, "Receiver".into(), "Pending".into()),
            (0, "Sender".into(), "Affirmed".into()),
        ]
    );
    chain
        .mediator_affirmation(
            rng,
            "mediator",
            "0",
            s3,
            0,
            0,
            true,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    // The instant receiver affirm binds the sender's affirmed leaf: end the block first.
    chain.end_block().unwrap();
    // Last pending affirmation: instant receiver affirm executes the settlement.
    chain
        .instant_receiver_affirmation(
            rng,
            "investor",
            "0",
            s3,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    assert_eq!(chain.store().settlement_status(s3).unwrap(), "Executed");
    // The counter-update proof binds the receiver's claimed leaf: end the block first.
    chain.end_block().unwrap();
    chain
        .sender_counter_update(
            rng,
            "issuer1",
            "0",
            s3,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    assert_eq!(chain.store().settlement_status(s3).unwrap(), "Finalized");

    // Finalized settlements keep only the tombstone: legs are pruned (LegNotFound after finalize).
    let s2_ref = chain.store().resolve_settlement_alias(s2).unwrap();
    assert!(chain.store().settlement_leg(&s2_ref, 0).unwrap().is_none());
}

#[test]
fn negative_paths_and_replay_guards() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-neg");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);
    let auditor_keys = chain
        .find_account("auditor", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset("issuer1", "a0", "A0", 6, &[], &[], &[auditor_keys.enc])
        .unwrap();
    chain
        .register_account_assets(
            rng,
            "issuer1",
            "0",
            asset,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();
    chain
        .mint_assets(
            rng,
            "issuer1",
            "0",
            asset,
            100,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();

    // MaxTotalSupplyExceeded: MAX_BALANCE = 2^48 - 1 (proof range) equals the default
    // `max_total_supply`, so minting the cap on top of the existing 100 overflows the supply.
    let err = chain
        .mint_assets(
            rng,
            "issuer1",
            "0",
            asset,
            polymesh_dart_common::MAX_BALANCE,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap_err();
    assert_eq!(err.name(), "MaxTotalSupplyExceeded");

    // NoAuditorsOrMediators
    let err = chain
        .create_asset("issuer1", "bad", "BAD", 6, &[], &[], &[])
        .unwrap_err();
    assert_eq!(err.name(), "NoAuditorsOrMediators");

    // NameTooLong / InvalidAssetName
    let err = chain
        .create_asset(
            "issuer1",
            &"n".repeat(2000),
            "X",
            6,
            &[],
            &[],
            &[auditor_keys.enc],
        )
        .unwrap_err();
    assert_eq!(err.name(), "NameTooLong");
    let err = chain
        .create_asset("issuer1", "", "X", 6, &[], &[], &[auditor_keys.enc])
        .unwrap_err();
    assert_eq!(err.name(), "InvalidAssetName");

    // Pallet metadata bounds are 100 / 20 / 8 (`polymesh_primitives::erc20`).
    let err = chain
        .create_asset(
            "issuer1",
            &"n".repeat(101),
            "X",
            6,
            &[],
            &[],
            &[auditor_keys.enc],
        )
        .unwrap_err();
    assert_eq!(err.name(), "NameTooLong");
    let err = chain
        .create_asset("issuer1", "ok", "X", 9, &[], &[], &[auditor_keys.enc])
        .unwrap_err();
    assert_eq!(err.name(), "TooManyDecimals");
    // A 20-byte symbol is within the pallet bound.
    let long_symbol_asset = chain
        .create_asset(
            "issuer1",
            "longsym",
            &"S".repeat(20),
            6,
            &[],
            &[],
            &[auditor_keys.enc],
        )
        .unwrap();
    assert_eq!(long_symbol_asset, 1);

    // AccountAssetAlreadyRegistered
    let err = chain
        .register_account_assets(
            rng,
            "issuer1",
            "0",
            asset,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap_err();
    assert_eq!(err.name(), "AccountAssetAlreadyRegistered");

    // SettlementAlreadyExists: replay the same settlement proof file.
    let legs = vec![(
        "issuer1".into(),
        "0".into(),
        "issuer2".into(),
        "0".into(),
        asset,
        10u64,
    )];
    let replay_file = dir.join("replay.proof");
    chain
        .create_settlement(
            rng,
            "replay",
            legs.clone(),
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::new(Some(replay_file.clone()), None, false).unwrap(),
        )
        .unwrap();
    chain
        .create_settlement(
            rng,
            "replay",
            legs.clone(),
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::new(None, Some(replay_file.clone()), false).unwrap(),
        )
        .unwrap();
    let err = chain
        .create_settlement(
            rng,
            "replay",
            legs,
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::new(None, Some(replay_file), false).unwrap(),
        )
        .unwrap_err();
    assert_eq!(err.name(), "SettlementAlreadyExists");
}

// ---------------------------------------------------------------- P1-8: fee accounts

fn fee(signer: &str, amount: polymesh_dart::Balance) -> (String, String, polymesh_dart::Balance) {
    (signer.to_string(), "0".to_string(), amount)
}

#[test]
fn fee_accounts_registration_topup_and_guards() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-fee");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);
    let ga = || ProofAction::GenerateAndApply { dry_run: false };

    // A duplicate account inside one batch is `FeeAccountAlreadyRegistered` (the pallet
    // inserts during its guard loop); it must not surface as an internal SQLite error.
    let err = chain
        .register_fee_accounts(
            rng,
            "issuer1",
            &[fee("issuer1", 10), fee("issuer1", 10)],
            ga(),
        )
        .unwrap_err();
    assert_eq!(err.name(), "FeeAccountAlreadyRegistered");
    assert_eq!(chain.store().fee_pool_balance().unwrap(), 0);

    // Registering a fee account deposits into the fee pool (pallet `fee_account_deposit`).
    chain
        .register_fee_accounts(rng, "issuer1", &[fee("issuer1", 100)], ga())
        .unwrap();
    assert_eq!(chain.store().fee_pool_balance().unwrap(), 100);
    chain.end_block().unwrap();

    // Re-registering the same fee account is rejected.
    let err = chain
        .register_fee_accounts(rng, "issuer1", &[fee("issuer1", 100)], ga())
        .unwrap_err();
    assert_eq!(err.name(), "FeeAccountAlreadyRegistered");

    // A fee account whose DART account belongs to another identity is `NotAccountOwner`.
    let err = chain
        .register_fee_accounts(rng, "issuer1", &[fee("investor", 100)], ga())
        .unwrap_err();
    assert_eq!(err.name(), "NotAccountOwner");

    // Top-up verifies against the fee-account tree root that contains the registered leaf.
    chain
        .topup_fee_accounts(rng, "issuer1", &[fee("issuer1", 200)], ga())
        .unwrap();
    assert_eq!(chain.store().fee_pool_balance().unwrap(), 300);
    chain.end_block().unwrap();

    // A second top-up round-trips through a fresh root (nullifier rotation).
    chain
        .topup_fee_accounts(rng, "issuer1", &[fee("issuer1", 50)], ga())
        .unwrap();
    assert_eq!(chain.store().fee_pool_balance().unwrap(), 350);

    // Top-up for a DART account with no fee account registration.
    let err = chain
        .topup_fee_accounts(rng, "investor", &[fee("investor", 50)], ga())
        .unwrap_err();
    assert_eq!(err.name(), "FeeAccountMissing");

    // Each registration/top-up appended exactly one append-only fee leaf.
    assert_eq!(
        chain.store().next_leaf_index(TreeKind::FeeAccount).unwrap(),
        3
    );
}

// ---------------------------------------------------------------- P1-9: batched proofs

use codec::Encode as _;

fn batch_of(specs: &[(&str, std::path::PathBuf)]) -> BatchedProofs<Limits> {
    fn dec<T: codec::DecodeWithMemTracking>(path: &std::path::Path) -> T {
        let bytes = std::fs::read(path).unwrap();
        T::decode(&mut &bytes[..]).unwrap()
    }
    let mut proofs = Vec::new();
    for (kind, path) in specs {
        let proof = match *kind {
            "create-settlement" => BatchedProof::CreateSettlement(dec(path)),
            "sender-affirm" => BatchedProof::SenderAffirmation(dec(path)),
            "receiver-affirm" => BatchedProof::ReceiverAffirmation(dec(path)),
            "mediator-affirm" => BatchedProof::MediatorAffirmation(dec(path), None),
            "sender-counter-update" => BatchedProof::SenderCounterUpdate(dec(path), None),
            "receiver-claim" => BatchedProof::ReceiverClaim(dec(path), None),
            // Explicit leg count, used to exercise `SettlementLegCountMismatch`.
            "receiver-claim-legs-99" => BatchedProof::ReceiverClaim(dec(path), Some(99)),
            other => panic!("unsupported batched kind {other}"),
        };
        proofs.push(proof);
    }
    BatchedProofs {
        proofs: bounded_collections::BoundedVec::try_from(proofs).unwrap(),
    }
}

#[test]
fn batched_proofs_atomic_apply() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-batch");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);
    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "a0",
            "A0",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    for signer in ["issuer1", "investor", "mediator"] {
        chain
            .register_account_assets(
                rng,
                signer,
                "0",
                asset,
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }
    chain.end_block().unwrap();
    chain
        .mint_assets(
            rng,
            "issuer1",
            "0",
            asset,
            1000,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();

    let gen = |name: &str| ProofAction::new(Some(dir.join(name)), None, false).unwrap();
    let apply = |name: &str| ProofAction::new(None, Some(dir.join(name)), false).unwrap();
    // Generation assigns the settlement alias, so parties can build proofs before the
    // settlement exists on chain.
    let legs = vec![(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        500u64,
    )];
    chain
        .create_settlement(
            rng,
            "batch-venue",
            legs.clone(),
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            gen("cs.proof"),
        )
        .unwrap();
    chain
        .sender_affirmation(rng, "issuer1", "0", 1, 0, &[], gen("sa.proof"))
        .unwrap();

    // Atomicity: the duplicate create-settlement fails after the first copy applied — the
    // whole batch rolls back, so the settlement does not exist and no leaf was appended.
    let leaves_before = chain.store().next_leaf_index(TreeKind::Account).unwrap();
    let bad = batch_of(&[
        ("create-settlement", dir.join("cs.proof")),
        ("create-settlement", dir.join("cs.proof")),
    ]);
    let err = chain.submit_batched_proofs(rng, &bad, false).unwrap_err();
    assert_eq!(err.name(), "SettlementAlreadyExists");
    assert_eq!(
        chain.store().next_leaf_index(TreeKind::Account).unwrap(),
        leaves_before
    );
    let err = chain.store().settlement_status(1).unwrap_err();
    assert_eq!(err.name(), "SettlementNotFound");

    // Valid batch: create + sender affirmation apply atomically.
    let batch = batch_of(&[
        ("create-settlement", dir.join("cs.proof")),
        ("sender-affirm", dir.join("sa.proof")),
    ]);
    chain.submit_batched_proofs(rng, &batch, false).unwrap();
    chain.end_block().unwrap();
    let legs = chain.store().show_legs(1).unwrap();
    assert!(legs.contains(&(0u8, "Sender".to_string(), "Affirmed".to_string())));

    // Standalone receiver + mediator affirmations (each needs its own committed root).
    chain
        .receiver_affirmation(rng, "investor", "0", 1, 0, &[], gen("ra.proof"))
        .unwrap();
    chain
        .receiver_affirmation(rng, "investor", "0", 1, 0, &[], apply("ra.proof"))
        .unwrap();
    chain.end_block().unwrap();
    chain
        .mediator_affirmation(rng, "mediator", "0", 1, 0, 0, true, gen("ma.proof"))
        .unwrap();
    chain
        .mediator_affirmation(rng, "mediator", "0", 1, 0, 0, true, apply("ma.proof"))
        .unwrap();
    chain.end_block().unwrap();

    // Batch [receiver-claim + sender-counter-update] finalizes the settlement in one tx.
    chain
        .receiver_claim(rng, "investor", "0", 1, 0, &[], gen("rc.proof"))
        .unwrap();
    chain
        .sender_counter_update(rng, "issuer1", "0", 1, 0, &[], gen("sc.proof"))
        .unwrap();
    // An explicit leg count that doesn't match the settlement is rejected before the proof
    // runs (`SettlementLegCountMismatch`), and nothing is applied.
    let wrong_legs = batch_of(&[("receiver-claim-legs-99", dir.join("rc.proof"))]);
    let err = chain
        .submit_batched_proofs(rng, &wrong_legs, false)
        .unwrap_err();
    assert_eq!(err.name(), "SettlementLegCountMismatch");
    assert_eq!(chain.store().settlement_status(1).unwrap(), "Executed");
    let batch = batch_of(&[
        ("receiver-claim", dir.join("rc.proof")),
        ("sender-counter-update", dir.join("sc.proof")),
    ]);
    chain.submit_batched_proofs(rng, &batch, false).unwrap();
    assert_eq!(chain.store().settlement_status(1).unwrap(), "Finalized");
}

// ---------------------------------------------------------------- P1-10: freeze & asset keys

#[test]
fn freeze_and_asset_key_updates() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-freeze");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);
    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let auditor_keys = chain
        .find_account("auditor", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "f0",
            "F0",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    for signer in ["issuer1", "investor", "mediator", "auditor"] {
        chain
            .register_account_assets(
                rng,
                signer,
                "0",
                asset,
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }
    chain.end_block().unwrap();

    // Issuer freeze / unfreeze round-trip.
    chain
        .set_asset_frozen(Some("issuer1"), asset, true)
        .unwrap();
    assert_eq!(
        chain.store().asset_frozen(asset).unwrap().as_deref(),
        Some("Issuer")
    );
    chain
        .set_asset_frozen(Some("issuer1"), asset, false)
        .unwrap();
    assert!(chain.store().asset_frozen(asset).unwrap().is_none());

    // Root freeze takes precedence: the issuer cannot unfreeze it (pallet `AssetFrozenByRoot`).
    chain.set_asset_frozen(None, asset, true).unwrap();
    assert_eq!(
        chain.store().asset_frozen(asset).unwrap().as_deref(),
        Some("Root")
    );
    let err = chain
        .set_asset_frozen(Some("issuer1"), asset, false)
        .unwrap_err();
    assert_eq!(err.name(), "AssetFrozenByRoot");
    // Only root can lift a root freeze.
    chain.set_asset_frozen(None, asset, false).unwrap();

    // Non-issuers cannot freeze or update keys.
    let err = chain
        .set_asset_frozen(Some("investor"), asset, true)
        .unwrap_err();
    assert_eq!(err.name(), "NotAssetOwner");
    let err = chain
        .update_asset_keys("investor", asset, &[], &[auditor_keys.enc])
        .unwrap_err();
    assert_eq!(err.name(), "NotAssetOwner");

    // `update_asset_keys` replaces the mediator set with the auditor and recomputes the leaf.
    let leaf_before = chain
        .store()
        .get_leaf(TreeKind::Asset, asset as u64)
        .unwrap();
    chain
        .update_asset_keys("issuer1", asset, &[], &[auditor_keys.enc])
        .unwrap();
    let leaf_after = chain
        .store()
        .get_leaf(TreeKind::Asset, asset as u64)
        .unwrap();
    assert_ne!(leaf_before, leaf_after);
    chain.end_block().unwrap();

    // `update_asset_keys` then reverts to the registered mediator set (leaves the asset
    // usable for settlements in later scenarios).
    chain
        .update_asset_keys(
            "issuer1",
            asset,
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    chain.end_block().unwrap();
}

// ---------------------------------------------------------------- P1-12: hidden asset id legs

#[test]
fn hidden_asset_id_leg_roundtrip() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-hidden");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);
    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "h0",
            "H0",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    for signer in ["issuer1", "investor", "mediator"] {
        chain
            .register_account_assets(
                rng,
                signer,
                "0",
                asset,
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }
    chain.end_block().unwrap();
    chain
        .mint_assets(
            rng,
            "issuer1",
            "0",
            asset,
            1000,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();

    let legs = vec![(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        400u64,
    )];
    // Hidden asset id: the leg embeds an asset membership proof, no revealed id.
    chain
        .create_settlement(
            rng,
            "hidden-venue",
            legs,
            false,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();

    chain
        .sender_affirmation(
            rng,
            "issuer1",
            "0",
            1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();
    chain
        .receiver_affirmation(
            rng,
            "investor",
            "0",
            1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();
    // Hidden legs use the leg's mediator encryption keys, keyed by `key_index` (P1-13).
    chain
        .mediator_affirmation(
            rng,
            "mediator",
            "0",
            1,
            0,
            0,
            true,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();
    assert_eq!(chain.store().settlement_status(1).unwrap(), "Executed");

    chain
        .receiver_claim(
            rng,
            "investor",
            "0",
            1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();
    chain
        .sender_counter_update(
            rng,
            "issuer1",
            "0",
            1,
            0,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    assert_eq!(chain.store().settlement_status(1).unwrap(), "Finalized");
}

// ---------------------------------------------------------------- P1-11: encryption keys & shared mediators

#[test]
fn encryption_keys_and_shared_mediators() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-keys");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);
    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "k0",
            "K0",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    for signer in ["issuer1", "investor", "mediator", "auditor"] {
        chain
            .register_account_assets(
                rng,
                signer,
                "0",
                asset,
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }
    chain.end_block().unwrap();
    chain
        .mint_assets(
            rng,
            "issuer1",
            "0",
            asset,
            1000,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();

    let ga = || ProofAction::GenerateAndApply { dry_run: false };

    // `register_encryption_keys` mints fresh host keys and registers them; replay fails.
    let ids = chain
        .register_encryption_keys(rng, "auditor", 2, ga())
        .unwrap();
    assert_eq!(ids.len(), 2);
    let replay_file = dir.join("reg-enc.proof");
    chain
        .register_encryption_keys(
            rng,
            "auditor",
            1,
            ProofAction::new(Some(replay_file.clone()), None, false).unwrap(),
        )
        .unwrap();
    chain
        .register_encryption_keys(
            rng,
            "auditor",
            1,
            ProofAction::new(None, Some(replay_file.clone()), false).unwrap(),
        )
        .unwrap();
    let err = chain
        .register_encryption_keys(
            rng,
            "auditor",
            1,
            ProofAction::new(None, Some(replay_file), false).unwrap(),
        )
        .unwrap_err();
    assert_eq!(err.name(), "EncryptionKeyAlreadyRegistered");

    // `distribute_encryption_key` registers the shared key under the auditor and records the
    // recipient (`SharedKeyRecipients`). The distributed key must NOT be on-chain yet, so we
    // generate one with a generation-only registration (host keystore key, unapplied).
    let dist_key_file = dir.join("dist-key.proof");
    let unregistered = chain
        .register_encryption_keys(
            rng,
            "auditor",
            1,
            ProofAction::new(Some(dist_key_file.clone()), None, false).unwrap(),
        )
        .unwrap();
    let shared_id = unregistered.last().copied().unwrap();

    let dist_file = dir.join("dist.proof");
    let got = chain
        .distribute_encryption_key(
            rng,
            "auditor",
            Some(shared_id),
            &[("mediator".to_string(), "0".to_string())],
            ProofAction::new(Some(dist_file.clone()), None, false).unwrap(),
        )
        .unwrap();
    assert_eq!(got, Some(shared_id));
    chain
        .distribute_encryption_key(
            rng,
            "auditor",
            Some(shared_id),
            &[("mediator".to_string(), "0".to_string())],
            ProofAction::new(None, Some(dist_file.clone()), false).unwrap(),
        )
        .unwrap();
    // Replaying the distribution proof hits the registration guard.
    let err = chain
        .distribute_encryption_key(
            rng,
            "auditor",
            Some(shared_id),
            &[("mediator".to_string(), "0".to_string())],
            ProofAction::new(None, Some(dist_file), false).unwrap(),
        )
        .unwrap_err();
    assert_eq!(err.name(), "EncryptionKeyAlreadyRegistered");
    chain.end_block().unwrap();

    // A mediator can carry the auditor's shared encryption key (`EncryptionKeyNotShared`
    // guard on the unshared key, success on the distributed one).
    let mediator_acct = mediator_keys.acct;
    // Registered on-chain keys that were never distributed are not shared keys.
    let unshared = chain.store().host_enc_key(ids[0]).unwrap().public;
    let err = chain
        .update_asset_keys("issuer1", asset, &[(mediator_acct, unshared)], &[])
        .unwrap_err();
    assert_eq!(err.name(), "EncryptionKeyNotShared");

    let shared_pub = chain.store().host_enc_key(shared_id).unwrap().public;
    chain
        .update_asset_keys("issuer1", asset, &[(mediator_acct, shared_pub)], &[])
        .unwrap();
    chain.end_block().unwrap();

    // Freeze/unfreeze must recommit the *stored* key set; re-deriving mediator keys from the
    // mediator account's own encryption key would drop the distributed shared key.
    let keys_before = chain.store().asset_keys(asset).unwrap().unwrap();
    let leaf_before = chain
        .store()
        .get_leaf(TreeKind::Asset, asset as u64)
        .unwrap();
    chain
        .set_asset_frozen(Some("issuer1"), asset, true)
        .unwrap();
    let keys_frozen = chain.store().asset_keys(asset).unwrap().unwrap();
    assert_eq!(keys_frozen.enc_keys, keys_before.enc_keys);
    assert_eq!(keys_frozen.mediators, keys_before.mediators);
    assert_ne!(
        chain
            .store()
            .get_leaf(TreeKind::Asset, asset as u64)
            .unwrap(),
        leaf_before
    );
    chain
        .set_asset_frozen(Some("issuer1"), asset, false)
        .unwrap();
    let keys_after = chain.store().asset_keys(asset).unwrap().unwrap();
    assert_eq!(keys_after.enc_keys, keys_before.enc_keys);
    assert_eq!(keys_after.mediators, keys_before.mediators);
    assert_eq!(
        chain
            .store()
            .get_leaf(TreeKind::Asset, asset as u64)
            .unwrap(),
        leaf_before
    );

    // Settlement over the shared-key mediator, full lifecycle.
    let legs = vec![(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        300u64,
    )];
    chain
        .create_settlement(
            rng,
            "shared-venue",
            legs,
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ga(),
        )
        .unwrap();
    chain.end_block().unwrap();
    chain
        .sender_affirmation(rng, "issuer1", "0", 1, 0, &[], ga())
        .unwrap();
    chain.end_block().unwrap();
    chain
        .receiver_affirmation(rng, "investor", "0", 1, 0, &[], ga())
        .unwrap();
    chain.end_block().unwrap();
    chain
        .mediator_affirmation(rng, "mediator", "0", 1, 0, 0, true, ga())
        .unwrap();
    chain.end_block().unwrap();
    chain
        .receiver_claim(rng, "investor", "0", 1, 0, &[], ga())
        .unwrap();
    chain.end_block().unwrap();
    chain
        .sender_counter_update(rng, "issuer1", "0", 1, 0, &[], ga())
        .unwrap();
    assert_eq!(chain.store().settlement_status(1).unwrap(), "Finalized");
}

// ---------------------------------------------------------------- P2: parity & scenario guards

#[test]
fn pallet_error_parity_table() {
    // Every pallet `ConfidentialAssetsError` variant has a same-named CLI error.
    let cli = dart_testing_cli::ChainError::all_names();
    for name in dart_testing_cli::PALLET_ERROR_NAMES {
        assert!(
            cli.contains(name),
            "missing CLI error for pallet variant {name}"
        );
    }
    // The CLI extras are exactly the transaction-level failures documented in the table.
    for name in cli {
        assert!(
            dart_testing_cli::PALLET_ERROR_NAMES.contains(&name)
                || matches!(name, "InsufficientBalance" | "Payment" | "BadOrigin"),
            "CLI error {name} is not in the parity table"
        );
    }
}

#[test]
fn stale_root_replay_and_leg_transplant() {
    // `ci-runtime` preset: short root-age windows so a few blocks expire a root.
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-stale");
    std::fs::create_dir_all(dir).unwrap();
    let db = dir.join("dart_test.db");
    let _ = std::fs::remove_file(&db);
    let chain = Chain::open(&db, TestConfig::ci_runtime()).unwrap();
    chain.initialize().unwrap();
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);

    ids(&chain, rng);
    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "s0",
            "S0",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    for signer in ["issuer1", "investor", "mediator"] {
        chain
            .register_account_assets(
                rng,
                signer,
                "0",
                asset,
                ProofAction::GenerateAndApply { dry_run: false },
            )
            .unwrap();
    }
    chain.end_block().unwrap();
    chain
        .mint_assets(
            rng,
            "issuer1",
            "0",
            asset,
            1000,
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain.end_block().unwrap();

    let gen = |name: &str| ProofAction::new(Some(dir.join(name)), None, false).unwrap();
    let apply = |name: &str| ProofAction::new(None, Some(dir.join(name)), false).unwrap();

    // Settlement 1 is created on-chain and its sender proof is generated (gen-only).
    let legs = vec![(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        100u64,
    )];
    chain
        .create_settlement(
            rng,
            "target",
            legs,
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            ProofAction::GenerateAndApply { dry_run: false },
        )
        .unwrap();
    chain
        .sender_affirmation(rng, "issuer1", "0", 1, 0, &[], gen("sa-s1.proof"))
        .unwrap();

    // Settlement 2 exists only as a generated proof + seeded legs (never applied).
    let legs2 = vec![(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        200u64,
    )];
    chain
        .create_settlement(
            rng,
            "ghost",
            legs2,
            true,
            dart_testing_cli::PartyVisibility::FullVisibility,
            &[],
            gen("cs-s2.proof"),
        )
        .unwrap();
    chain
        .sender_affirmation(rng, "issuer1", "0", 2, 0, &[], gen("sa-s2.proof"))
        .unwrap();
    chain.end_block().unwrap();

    // Transplant guard: settlement 2's sender proof applied while settlement 2 does not
    // exist on-chain fails against the settlement the *proof* references.
    let err = chain
        .sender_affirmation(rng, "issuer1", "0", 2, 0, &[], apply("sa-s2.proof"))
        .unwrap_err();
    assert_eq!(err.name(), "SettlementNotFound");

    // Stale root replay: advance blocks until the account root settlement 1's sender
    // proof references falls outside the (short) ci-runtime max age.
    for _ in 0..130 {
        chain.end_block().unwrap();
    }
    let err = chain
        .sender_affirmation(rng, "issuer1", "0", 1, 0, &[], apply("sa-s1.proof"))
        .unwrap_err();
    assert_eq!(err.name(), "CurveTreeRootNotFound");
}

// ---------------------------------------------------------------- seed persistence

#[test]
fn seed_is_persisted_and_defaults_for_later_commands() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-seed");
    let chain = setup(dir);
    chain.store().set_run_seed("0000000000000001").unwrap();
    assert_eq!(
        chain.store().run_seed().unwrap().as_deref(),
        Some("0000000000000001")
    );

    // A later command with no explicit seed resolves to the stored one.
    assert_eq!(
        dart_testing_cli::resolve_run_seed(None, chain.store()).unwrap(),
        1
    );
    // An explicit seed still wins.
    assert_eq!(
        dart_testing_cli::resolve_run_seed(Some("2"), chain.store()).unwrap(),
        2
    );

    // The per-command seed mixes chain progress and is stable for the same state.
    let derived = dart_testing_cli::derive_command_seed(1, chain.store()).unwrap();
    assert_eq!(
        derived,
        dart_testing_cli::derive_command_seed(1, chain.store()).unwrap()
    );
    chain.create_signer("seed-signer").unwrap();
    chain.end_block().unwrap();
    assert_ne!(
        derived,
        dart_testing_cli::derive_command_seed(1, chain.store()).unwrap()
    );
    drop(chain);

    // The stored seed survives reopening the database.
    let reopened = Chain::open(dir.join("dart_test.db"), TestConfig::default()).unwrap();
    assert_eq!(
        reopened.store().run_seed().unwrap().as_deref(),
        Some("0000000000000001")
    );
    assert_eq!(
        dart_testing_cli::resolve_run_seed(None, reopened.store()).unwrap(),
        1
    );
}

// ---------------------------------------------------------------- relayer path

#[test]
fn relayer_batches_pay_fee_and_bind_context() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-relayer");
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);
    let ga = || ProofAction::GenerateAndApply { dry_run: false };

    ids(&chain, rng);
    chain.create_signer("relayer").unwrap();
    chain.create_account(rng, "relayer", "0").unwrap();
    chain.register_accounts(rng, "relayer", "0", ga()).unwrap();

    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "fee",
            "FEE",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    for signer in ["issuer1", "investor", "mediator"] {
        chain
            .register_account_assets(rng, signer, "0", asset, ga())
            .unwrap();
    }
    chain.end_block().unwrap();
    chain
        .mint_assets(rng, "issuer1", "0", asset, 1000, ga())
        .unwrap();
    chain.end_block().unwrap();

    chain
        .register_fee_accounts(rng, "relayer", &[fee("relayer", 100)], ga())
        .unwrap();
    chain.end_block().unwrap();
    assert_eq!(chain.store().fee_pool_balance().unwrap(), 100);

    // The relayer's next payment nullifier, and the context every party proof must bind.
    let nullifier = chain.relayer_fee_preview("relayer", "0", 20).unwrap();
    let ctx = polymesh_dart::relayer_batch_proof_context(&nullifier);

    let gen = |name: &str| ProofAction::new(Some(dir.join(name)), None, false).unwrap();
    let legs = vec![(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        300u64,
    )];
    chain
        .create_settlement_with_context(
            rng,
            "relayer-venue",
            legs,
            true,
            PartyVisibility::FullVisibility,
            &[],
            &ctx,
            gen("cs.proof"),
        )
        .unwrap();
    chain
        .sender_affirmation(rng, "issuer1", "0", 1, 0, &ctx, gen("sa.proof"))
        .unwrap();
    chain
        .receiver_affirmation(rng, "investor", "0", 1, 0, &ctx, gen("ra.proof"))
        .unwrap();
    chain
        .mediator_affirmation_with_context(
            rng,
            "mediator",
            "0",
            1,
            0,
            0,
            true,
            &ctx,
            gen("ma.proof"),
        )
        .unwrap();

    let batch = batch_of(&[
        ("create-settlement", dir.join("cs.proof")),
        ("sender-affirm", dir.join("sa.proof")),
        ("receiver-affirm", dir.join("ra.proof")),
        ("mediator-affirm", dir.join("ma.proof")),
    ]);
    let fee_path = dir.join("relayer-payment.proof");
    chain
        .relayer_batched_proofs_new(rng, "relayer", "0", batch, 20, false, &fee_path)
        .unwrap();
    let fee_proof: FeePaymentWithBatchedProofs<Limits> =
        codec::Decode::decode(&mut &std::fs::read(&fee_path).unwrap()[..]).unwrap();
    chain
        .relayer_batched_proofs_apply(rng, "relayer", "0", &fee_proof, false)
        .unwrap();

    assert_eq!(chain.store().settlement_status(1).unwrap(), "Executed");
    assert_eq!(chain.store().fee_pool_balance().unwrap(), 80);
    // The batch outcome event is recorded on the batch dispatch, not dropped.
    let traces = chain.store().read_trace().unwrap();
    assert!(traces.iter().any(|t| {
        t.call == "relayer_batched_proofs"
            && t.outcome == "Ok"
            && t.events
                .iter()
                .any(|(e, d)| e == "RelayerBatchedProofs" && d.contains("batch_result=Ok"))
    }));
    // The paid fee state was promoted: the next preview is a fresh nullifier.
    let after_success = chain.relayer_fee_preview("relayer", "0", 20).unwrap();
    assert_ne!(after_success.encode(), nullifier.encode());

    // The relayer batch applied issuer1's sender affirmation; its prover state must have been
    // promoted, so a new proof from that account must work (regression: a stale state would
    // reuse the burned nullifier).
    chain.end_block().unwrap();
    chain
        .mint_assets(rng, "issuer1", "0", asset, 10, ga())
        .unwrap();
    chain.end_block().unwrap();

    // A failed batch still pays the fee, records the outcome, and advances the host fee state.
    let failed_nullifier = chain.relayer_fee_preview("relayer", "0", 20).unwrap();
    let bad_batch = batch_of(&[("create-settlement", dir.join("cs.proof"))]);
    let bad_fee_path = dir.join("relayer-payment-failed.proof");
    chain
        .relayer_batched_proofs_new(rng, "relayer", "0", bad_batch, 20, false, &bad_fee_path)
        .unwrap();
    let bad_proof: FeePaymentWithBatchedProofs<Limits> =
        codec::Decode::decode(&mut &std::fs::read(&bad_fee_path).unwrap()[..]).unwrap();
    let err = chain
        .relayer_batched_proofs_apply(rng, "relayer", "0", &bad_proof, false)
        .unwrap_err();
    assert_eq!(err.name(), "SettlementAlreadyExists");
    assert_eq!(chain.store().fee_pool_balance().unwrap(), 60);
    let traces = chain.store().read_trace().unwrap();
    assert!(traces.iter().any(|t| {
        t.call == "relayer_batched_proofs"
            && t.error.as_deref() == Some("SettlementAlreadyExists")
            && t.events.iter().any(|(e, d)| {
                e == "RelayerBatchedProofs" && d.contains("batch_result=SettlementAlreadyExists")
            })
    }));
    let after_failure = chain.relayer_fee_preview("relayer", "0", 20).unwrap();
    assert_ne!(after_failure.encode(), failed_nullifier.encode());
}

// ---------------------------------------------------------------- corpus record/replay

#[test]
fn corpus_records_and_replays() {
    let dir = std::path::Path::new("/tmp/opencode/dart-cli-test-corpus");
    for name in ["corpus.jsonl", "session.db", "replay.db"] {
        let _ = std::fs::remove_file(dir.join(name));
    }
    let chain = setup(dir);
    let base_rng = &mut thread_rng();
    let rng = &mut reseed_rng(base_rng);
    let ga = || ProofAction::GenerateAndApply { dry_run: false };

    // `init` stores the seed before a recorder is attached.
    chain.store().set_run_seed("0000000000000001").unwrap();
    let corpus = dir.join("corpus.jsonl");
    chain.attach_recorder(&corpus).unwrap();

    ids(&chain, rng);
    let mediator_keys = chain
        .find_account("mediator", "0")
        .unwrap()
        .account_keys()
        .unwrap()
        .public_keys();
    let asset = chain
        .create_asset(
            "issuer1",
            "c0",
            "C0",
            6,
            &[],
            &[(mediator_keys.acct, mediator_keys.enc)],
            &[],
        )
        .unwrap();
    for signer in ["issuer1", "investor"] {
        chain
            .register_account_assets(rng, signer, "0", asset, ga())
            .unwrap();
    }
    chain.end_block().unwrap();
    chain
        .mint_assets(rng, "issuer1", "0", asset, 1000, ga())
        .unwrap();
    chain.end_block().unwrap();

    // Generate/apply/replay a settlement creation: the replay is recorded as a failure.
    let legs = vec![(
        "issuer1".to_string(),
        "0".to_string(),
        "investor".to_string(),
        "0".to_string(),
        asset,
        100u64,
    )];
    let cs = dir.join("cs.proof");
    chain
        .create_settlement(
            rng,
            "corpus",
            legs.clone(),
            true,
            PartyVisibility::FullVisibility,
            &[],
            ProofAction::new(Some(cs.clone()), None, false).unwrap(),
        )
        .unwrap();
    chain
        .create_settlement(
            rng,
            "corpus",
            legs.clone(),
            true,
            PartyVisibility::FullVisibility,
            &[],
            ProofAction::new(None, Some(cs.clone()), false).unwrap(),
        )
        .unwrap();
    let err = chain
        .create_settlement(
            rng,
            "corpus",
            legs,
            true,
            PartyVisibility::FullVisibility,
            &[],
            ProofAction::new(None, Some(cs), false).unwrap(),
        )
        .unwrap_err();
    assert_eq!(err.name(), "SettlementAlreadyExists");

    chain
        .sender_affirmation(rng, "issuer1", "0", 1, 0, &[], ga())
        .unwrap();
    chain.end_block().unwrap();
    chain
        .receiver_affirmation(rng, "investor", "0", 1, 0, &[], ga())
        .unwrap();
    chain.end_block().unwrap();
    chain
        .mediator_affirmation(rng, "mediator", "0", 1, 0, 0, true, ga())
        .unwrap();
    chain.end_block().unwrap();
    assert_eq!(chain.store().settlement_status(1).unwrap(), "Executed");

    // The recording session owns its own chain snapshot (separate from the main DB).
    let session_db = dir.join("session.db");
    chain.store().snapshot_to(&session_db).unwrap();
    let snapshot = Chain::open(&session_db, TestConfig::default()).unwrap();
    assert_eq!(snapshot.store().settlement_status(1).unwrap(), "Executed");

    let records = dart_testing_cli::corpus::read_records(&corpus).unwrap();
    assert!(records.len() > 10);
    assert!(records
        .iter()
        .any(|record| record.outcome == "SettlementAlreadyExists"));

    // Resetting the main DB must not lose the corpus.
    chain.initialize().unwrap();
    assert_eq!(
        dart_testing_cli::corpus::read_records(&corpus)
            .unwrap()
            .len(),
        records.len()
    );

    // Replay into a fresh scratch DB (never the main DB).
    let header = dart_testing_cli::corpus::read_header(&corpus).unwrap();
    let replay_db = dir.join("replay.db");
    let replayed = Chain::open(&replay_db, header.config.clone()).unwrap();
    replayed.initialize().unwrap();
    replayed.store().set_run_seed(&header.seed).unwrap();
    let summary = dart_testing_cli::corpus::replay(&replayed, &corpus, false).unwrap();
    assert_eq!(summary.total, records.len());
    assert!(
        summary.mismatches.is_empty(),
        "unexpected replay mismatches: {:?}",
        summary.mismatches
    );
    assert_eq!(replayed.store().settlement_status(1).unwrap(), "Executed");
}
