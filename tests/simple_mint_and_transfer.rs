use anyhow::Result;
use test_log::test;

use polymesh_dart::*;

mod common;
use common::*;

/// This test simulates a simple mint and transfer of assets between the asset issuer and an investor.
///
/// The asset has a mediator who must also affirm the settlement.
#[test]
fn test_mint_and_transfer_with_mediator() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Setup chain state.
    let mut chain = DartChainState::new()?;

    // Setup an off-chain curve-tree prover.
    let mut account_tree = DartProverAccountTree::new()?;
    account_tree.apply_updates(&chain)?;

    // Create some users.
    let users = chain.create_signers(&["AssetIssuer", "Mediator", "Investor1"])?;
    let mut issuer = DartUser::new(&users[0]);
    let mut mediator = DartUser::new(&users[1]);
    let mut investor1 = DartUser::new(&users[2]);

    // Create account keys and register them for the issuer, mediator, and investor.
    let issuer_acct = issuer.create_and_register_account(&mut rng, &mut chain, "1")?;
    let mediator_acct = mediator.create_and_register_account(&mut rng, &mut chain, "1")?;
    let investor1_acct = investor1.create_and_register_account(&mut rng, &mut chain, "1")?;

    eprintln!("Issuer account: {:?}", issuer_acct.public_keys());
    eprintln!("Mediator account: {:?}", mediator_acct.public_keys());
    eprintln!("Investor account: {:?}", investor1_acct.public_keys());

    // Create a Dart asset with the issuer as the owner and the mediator as the auditor.
    let asset_id = issuer.create_asset(&mut chain, &[], &[mediator_acct.public_keys().enc])?;
    let asset = chain.get_asset_state(asset_id)?;

    // Initialize account asset state for the issuer and investor.
    issuer_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;
    investor1_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Mint the asset to the issuer's account.
    issuer_acct.mint_asset(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        asset_id,
        1000,
    )?;

    // Create a settlement to transfer some assets from the issuer to the investor.
    let settlement = SettlementBuilder::new(b"Test")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset,
            amount: 500,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;
    // Submit the settlement.
    let settlement_id = issuer.create_settlement(&mut chain, settlement)?;
    let leg_ref = LegRef::new(settlement_id.into(), 0);

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // The issuer affirms the settlement as the sender.
    issuer_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
        asset_id,
        500,
    )?;

    // The investor affirms the settlement as the receiver.
    investor1_acct.receiver_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
        asset_id,
        500,
    )?;

    // The mediator affirms the settlement.
    mediator_acct.mediator_affirmation(&mut rng, &mut chain, &leg_ref, true)?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // The settlement should have executed.

    // Receiver claims their assets.
    investor1_acct.receiver_claims(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
    )?;

    Ok(())
}

/// Mint and transfer an asset that only has an auditor, not a mediator.
///
/// This test simulates a simple mint and transfer of assets between the asset issuer and an investor.
///
/// Steps:
/// 1. Create an asset issuer, an auditor, and an investor.
/// 2. The asset issuer creates an asset with the auditor and mints it to their account.
/// 3. The investor creates and initializes their account for the asset.
/// 4. The asset issuer creates a settlement to transfer assets to the investor.
/// 5. The asset issuer affirms the settlement as the sender.
/// 6. The investor affirms the settlement as the receiver.
/// 7. THe auditor decrypts the leg details.
/// 8. The investor claims the assets from the settlement.
/// 9. The asset issuer updates their sender counter to finalize the settlement.
#[test]
fn test_mint_and_transfer_with_auditor() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Setup chain state.
    let mut chain = DartChainState::new()?;

    // Setup an off-chain curve-tree prover.
    let mut account_tree = DartProverAccountTree::new()?;
    account_tree.apply_updates(&chain)?;

    // Create some users.
    let users = chain.create_signers(&["AssetIssuer", "Auditor", "Investor1"])?;
    let mut issuer = DartUser::new(&users[0]);
    let mut auditor = DartUser::new(&users[1]);
    let mut investor1 = DartUser::new(&users[2]);

    // Create account keys and register them for the issuer, auditor, and investor.
    let issuer_acct = issuer.create_and_register_account(&mut rng, &mut chain, "1")?;
    let auditor_acct = auditor.create_and_register_account(&mut rng, &mut chain, "1")?;
    let auditor_enc = auditor_acct.public_keys().enc.clone();
    let investor1_acct = investor1.create_and_register_account(&mut rng, &mut chain, "1")?;

    eprintln!("Issuer account: {:?}", issuer_acct.public_keys());
    eprintln!("Auditor account: {:?}", auditor_acct.public_keys());
    eprintln!("Investor account: {:?}", investor1_acct.public_keys());

    // Create a Dart asset with the issuer as the owner and the auditor as the auditor.
    let asset_id = issuer.create_asset(&mut chain, &[auditor_enc], &[])?;
    let asset = chain.get_asset_state(asset_id)?;

    // Initialize account asset state for the issuer and investor.
    issuer_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;
    investor1_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Mint the asset to the issuer's account.
    issuer_acct.mint_asset(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        asset_id,
        1000,
    )?;

    // Create a settlement to transfer some assets from the issuer to the investor.
    let settlement = SettlementBuilder::new(b"Test")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset,
            amount: 500,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;
    // Submit the settlement.
    let settlement_id = issuer.create_settlement(&mut chain, settlement)?;
    let leg_ref = LegRef::new(settlement_id.into(), 0);

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // The issuer affirms the settlement as the sender.
    issuer_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
        asset_id,
        500,
    )?;

    // The investor affirms the settlement as the receiver.
    investor1_acct.receiver_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
        asset_id,
        500,
    )?;

    // The auditor decrypts the leg details.
    let leg = auditor_acct.decrypt_leg(&chain, &leg_ref, LegRole::Auditor(0))?;
    // Verify the leg details.
    assert_eq!(leg.sender()?, issuer_acct.public_keys().acct);
    assert_eq!(leg.receiver()?, investor1_acct.public_keys().acct);
    assert_eq!(leg.asset_id(), asset_id);
    assert_eq!(leg.amount(), 500);

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // The investor claims the assets from the settlement.
    investor1_acct.receiver_claims(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
    )?;

    // The issuer updates their sender counter to finalize the settlement.
    issuer_acct.sender_counter_update(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
    )?;

    // Ensure the settlement is finalized.
    assert_eq!(
        chain.get_settlement_status(settlement_id)?,
        SettlementStatus::Finalized
    );

    Ok(())
}

/// Test an atomic swap using two assets created by different asset issuers.
///
/// Steps:
/// 1. Create two asset issuers, one auditor, one mediator and two investors.
/// 2. Each asset issuer creates an asset (one asset has an auditor the other has a mediator) and mints it to their respective accounts.
/// 3. The investors create and initialize their accounts for the assets.
/// 4. The asset issuers create settlements to fund the investors' accounts.
/// 5. The asset issuers, mediator and investors affirm the settlements.
/// 6. The investors claim the assets.
/// 7. The investors setup a settlement to do an atomic swap between the two assets.
/// 8. The investors affirm the settlement.
/// 9. The mediator affirms the settlement.
/// 10. The investors claim the assets from the settlement.
/// 11. The asset issuers need to update their counters (as the sender in the funding settlement) to finalize the funding settlements.
/// 12. The investors need to update their counters (as the sender in the atomic swap settlement) to finalize the all settlements.
/// 13. All settlements should be finalized.
#[test]
fn test_atomic_swap() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Setup chain state.
    let mut chain = DartChainState::new()?;

    // Setup an off-chain curve-tree prover.
    let mut account_tree = DartProverAccountTree::new()?;
    account_tree.apply_updates(&chain)?;

    // Step 1: Create two asset issuers, one auditor, one mediator and two investors.
    let users = chain.create_signers(&[
        "AssetIssuer1",
        "AssetIssuer2",
        "Auditor",
        "Mediator",
        "Investor1",
        "Investor2",
    ])?;
    let mut issuer1 = DartUser::new(&users[0]);
    let mut issuer2 = DartUser::new(&users[1]);
    let mut auditor = DartUser::new(&users[2]);
    let mut mediator = DartUser::new(&users[3]);
    let mut investor1 = DartUser::new(&users[4]);
    let mut investor2 = DartUser::new(&users[5]);

    // Create account keys and register them for all users.
    let issuer1_acct = issuer1.create_and_register_account(&mut rng, &mut chain, "1")?;
    let issuer2_acct = issuer2.create_and_register_account(&mut rng, &mut chain, "1")?;
    let auditor_acct = auditor.create_and_register_account(&mut rng, &mut chain, "1")?;
    let mediator_acct = mediator.create_and_register_account(&mut rng, &mut chain, "1")?;
    let investor1_acct = investor1.create_and_register_account(&mut rng, &mut chain, "1")?;
    let investor2_acct = investor2.create_and_register_account(&mut rng, &mut chain, "1")?;

    // Step 2: Each asset issuer creates an asset (one asset has an auditor the other has a mediator) and mints it to their respective accounts.
    let asset1_id = issuer1.create_asset(&mut chain, &[auditor_acct.public_keys().enc], &[])?;
    let asset1 = chain.get_asset_state(asset1_id)?;
    let asset2_id = issuer2.create_asset(&mut chain, &[], &[mediator_acct.public_keys().enc])?;
    let asset2 = chain.get_asset_state(asset2_id)?;

    // Initialize account asset state for the issuers.
    issuer1_acct.initialize_asset(&mut rng, &mut chain, asset1_id)?;
    issuer2_acct.initialize_asset(&mut rng, &mut chain, asset2_id)?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Mint the assets to the issuers' accounts.
    issuer1_acct.mint_asset(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        asset1_id,
        2000,
    )?;
    issuer2_acct.mint_asset(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        asset2_id,
        3000,
    )?;

    // Step 3: The investors create and initialize their accounts for the assets.
    investor1_acct.initialize_asset(&mut rng, &mut chain, asset1_id)?;
    investor1_acct.initialize_asset(&mut rng, &mut chain, asset2_id)?;
    investor2_acct.initialize_asset(&mut rng, &mut chain, asset1_id)?;
    investor2_acct.initialize_asset(&mut rng, &mut chain, asset2_id)?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 4: The asset issuers create settlements to fund the investors' accounts.
    // Issuer1 sends asset1 to investor1
    let funding_settlement1 = SettlementBuilder::new(b"Funding1")
        .leg(LegBuilder {
            sender: issuer1_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset: asset1.clone(),
            amount: 1000,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;
    eprintln!("Creating funding settlement: {:?}", funding_settlement1);
    let funding_settlement1_id = issuer1.create_settlement(&mut chain, funding_settlement1)?;
    let funding_leg1_ref = LegRef::new(funding_settlement1_id.into(), 0);

    // Issuer2 sends asset2 to investor2
    let funding_settlement2 = SettlementBuilder::new(b"Funding2")
        .leg(LegBuilder {
            sender: issuer2_acct.public_keys(),
            receiver: investor2_acct.public_keys(),
            asset: asset2.clone(),
            amount: 1500,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;
    eprintln!("Creating funding settlement: {:?}", funding_settlement2);
    let funding_settlement2_id = issuer2.create_settlement(&mut chain, funding_settlement2)?;
    let funding_leg2_ref = LegRef::new(funding_settlement2_id.into(), 0);

    // End the block to finalize the settlements.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 5: The asset issuers, mediator and investors affirm the funding settlements.
    // Funding settlement 1 affirmations
    eprintln!("Issuer1 affirming funding settlement leg 1");
    issuer1_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg1_ref,
        asset1_id,
        1000,
    )?;
    eprintln!("Investor1 affirming funding settlement leg 1");
    investor1_acct.receiver_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg1_ref,
        asset1_id,
        1000,
    )?;
    // Note: Asset1 has an auditor, not a mediator, so no mediator affirmation needed

    // Funding settlement 2 affirmations
    eprintln!("Issuer2 affirming funding settlement leg 2");
    issuer2_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg2_ref,
        asset2_id,
        1500,
    )?;
    eprintln!("Investor2 affirming funding settlement leg 2");
    investor2_acct.receiver_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg2_ref,
        asset2_id,
        1500,
    )?;
    eprintln!("Mediator affirming funding settlement leg 2");
    mediator_acct.mediator_affirmation(&mut rng, &mut chain, &funding_leg2_ref, true)?;

    // End the block to finalize the affirmations.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 6: The investors claim the assets.
    eprintln!("Investor1 claiming asset1 from funding settlement leg 1");
    investor1_acct.receiver_claims(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg1_ref,
    )?;
    eprintln!("Investor1 claimed asset1 from funding settlement leg 1");
    investor2_acct.receiver_claims(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg2_ref,
    )?;

    // End the block to finalize the claims.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 7: The investors setup a settlement to do an atomic swap between the two assets.
    // Investor1 sends asset1 to investor2, investor2 sends asset2 to investor1
    let swap_settlement = SettlementBuilder::new(b"AtomicSwap")
        .leg(LegBuilder {
            sender: investor1_acct.public_keys(),
            receiver: investor2_acct.public_keys(),
            asset: asset1,
            amount: 500,
        })
        .leg(LegBuilder {
            sender: investor2_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset: asset2,
            amount: 750,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;
    eprintln!("Creating swap settlement: {:?}", swap_settlement);
    let swap_settlement_id = investor1.create_settlement(&mut chain, swap_settlement)?;
    let swap_leg1_ref = LegRef::new(swap_settlement_id.into(), 0);
    let swap_leg2_ref = LegRef::new(swap_settlement_id.into(), 1);

    // End the block to finalize the swap settlement.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 8: The investors affirm the settlement.
    // Investor1 affirms as sender for leg 1 and receiver for leg 2
    eprintln!("Investor1 affirming swap settlement leg 1");
    investor1_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg1_ref,
        asset1_id,
        500,
    )?;
    eprintln!("Investor1 affirming swap settlement leg 2");
    investor1_acct.receiver_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg2_ref,
        asset2_id,
        750,
    )?;

    // Investor2 affirms as receiver for leg 1 and sender for leg 2
    eprintln!("Investor2 affirming swap settlement leg 1");
    investor2_acct.receiver_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg1_ref,
        asset1_id,
        500,
    )?;
    eprintln!("Investor2 affirming swap settlement leg 2");
    investor2_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg2_ref,
        asset2_id,
        750,
    )?;

    // Step 9: The mediator affirms the settlement.
    // Note: Only asset2 has a mediator, asset1 has an auditor
    eprintln!("Mediator affirming swap settlement leg 2");
    mediator_acct.mediator_affirmation(&mut rng, &mut chain, &swap_leg2_ref, true)?;

    // End the block to finalize the affirmations.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 10: The investors claim the assets from the settlement.
    eprintln!("Investor1 claiming asset1 from swap settlement leg 1");
    investor1_acct.receiver_claims(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg2_ref,
    )?;
    eprintln!("Investor2 claiming asset2 from swap settlement leg 2");
    investor2_acct.receiver_claims(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg1_ref,
    )?;

    // End the block to finalize the affirmations.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 11: The asset issuers need to update their counters (as the sender in the funding settlement) to finalize the funding settlements.
    eprintln!("Issuer1 updating sender counter for funding settlement 1");
    issuer1_acct.sender_counter_update(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg1_ref,
    )?;
    eprintln!("Issuer2 updating sender counter for funding settlement 2");
    issuer2_acct.sender_counter_update(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &funding_leg2_ref,
    )?;

    // End the block to finalize the affirmations.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 12: The investors need to update their counters (as the sender in the atomic swap settlement) to finalize the all settlements.
    eprintln!("Investor1 updating sender counter for swap settlement leg 1");
    investor1_acct.sender_counter_update(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg1_ref,
    )?;
    eprintln!("Investor2 updating sender counter for swap settlement leg 2");
    investor2_acct.sender_counter_update(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &swap_leg2_ref,
    )?;

    // End the block to finalize the affirmations.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 13: All settlements should be finalized.
    eprintln!("Checking settlement statuses...");
    assert_eq!(
        chain.get_settlement_status(funding_settlement1_id)?,
        SettlementStatus::Finalized
    );
    assert_eq!(
        chain.get_settlement_status(funding_settlement2_id)?,
        SettlementStatus::Finalized
    );
    assert_eq!(
        chain.get_settlement_status(swap_settlement_id)?,
        SettlementStatus::Finalized
    );

    Ok(())
}

/// Test rejecting a settlement after the sender has affirmed it and have the sender revert the affirmation.
///
/// This test simulates a scenario where the sender affirms a settlement, but then the settlement is rejected by the mediator.
///
/// Steps:
/// 1. Create an asset issuer, a mediator, and an investor.
/// 2. The asset issuer creates an asset and mints it to their account.
/// 3. The investor creates and initializes their account for the asset.
/// 4. The asset issuer creates a settlement to transfer assets to the investor.
/// 5. The asset issuer affirms the settlement as the sender.
/// 6. The mediator rejects the settlement.
/// 7. The sender reverts their affirmation.
#[test]
fn test_reject_after_sender_affirms() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Setup chain state.
    let mut chain = DartChainState::new()?;

    // Setup an off-chain curve-tree prover.
    let mut account_tree = DartProverAccountTree::new()?;
    account_tree.apply_updates(&chain)?;

    // Step 1: Create an asset issuer, a mediator, and an investor.
    let users = chain.create_signers(&["AssetIssuer", "Mediator", "Investor"])?;
    let mut issuer = DartUser::new(&users[0]);
    let mut mediator = DartUser::new(&users[1]);
    let mut investor = DartUser::new(&users[2]);

    // Create account keys and register them for all users.
    let issuer_acct = issuer.create_and_register_account(&mut rng, &mut chain, "1")?;
    let mediator_acct = mediator.create_and_register_account(&mut rng, &mut chain, "1")?;
    let investor_acct = investor.create_and_register_account(&mut rng, &mut chain, "1")?;

    // Step 2: The asset issuer creates an asset and mints it to their account.
    let asset_id = issuer.create_asset(&mut chain, &[], &[mediator_acct.public_keys().enc])?;
    let asset = chain.get_asset_state(asset_id)?;

    // Initialize account asset state for the issuer and investor.
    issuer_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;
    investor_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Mint the asset to the issuer's account.
    issuer_acct.mint_asset(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        asset_id,
        1000,
    )?;

    // Step 3: The investor creates and initializes their account for the asset.
    // (Already done above)

    // Step 4: The asset issuer creates a settlement to transfer assets to the investor.
    let settlement = SettlementBuilder::new(b"TestReject")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor_acct.public_keys(),
            asset,
            amount: 500,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;

    let settlement_id = issuer.create_settlement(&mut chain, settlement)?;
    let leg_ref = LegRef::new(settlement_id.into(), 0);

    // End the block to finalize the settlement.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Step 5: The asset issuer affirms the settlement as the sender.
    issuer_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
        asset_id,
        500,
    )?;

    // End the block to finalize the sender affirmation.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Verify the settlement is still pending (waiting for receiver and mediator)
    assert_eq!(
        chain.get_settlement_status(settlement_id)?,
        SettlementStatus::Pending
    );

    // Step 6: The mediator rejects the settlement.
    mediator_acct.mediator_affirmation(&mut rng, &mut chain, &leg_ref, false)?;

    // End the block to finalize the mediator rejection.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Verify the settlement is now rejected
    assert_eq!(
        chain.get_settlement_status(settlement_id)?,
        SettlementStatus::Rejected
    );

    // Step 7: The sender reverts their affirmation.
    issuer_acct.sender_revert(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
    )?;

    // End the block to finalize the sender revert.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Verify the settlement is still rejected but the sender has finalized their leg
    assert_eq!(
        chain.get_settlement_status(settlement_id)?,
        SettlementStatus::Finalized
    );

    Ok(())
}

/// Test if the sender can falsely affirm as the receiver in a settlement.
///
/// This test should fail because the sender should not be able to affirm as the receiver.
#[test]
fn test_sender_tries_to_affirms_for_receiver() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Setup chain state.
    let mut chain = DartChainState::new().expect("Failed to create DartChainState");

    // Setup an off-chain curve-tree prover.
    let mut account_tree =
        DartProverAccountTree::new().expect("Failed to create DartProverAccountTree");
    account_tree
        .apply_updates(&chain)
        .expect("Failed to apply updates to account tree");

    // Create some users.
    let users = chain
        .create_signers(&["AssetIssuer", "Auditor", "Investor1"])
        .expect("Failed to create signers");
    let mut issuer = DartUser::new(&users[0]);
    let mut auditor = DartUser::new(&users[1]);
    let mut investor1 = DartUser::new(&users[2]);

    // Create account keys and register them for the issuer, auditor, and investor.
    let issuer_acct = issuer.create_and_register_account(&mut rng, &mut chain, "1")?;
    let auditor_acct = auditor.create_and_register_account(&mut rng, &mut chain, "1")?;
    let auditor_enc = auditor_acct.public_keys().enc.clone();
    let investor1_acct = investor1.create_and_register_account(&mut rng, &mut chain, "1")?;

    // Create a Dart asset with the issuer as the owner and the auditor as the auditor.
    let asset_id = issuer.create_asset(&mut chain, &[auditor_enc], &[])?;
    let asset = chain.get_asset_state(asset_id)?;

    // Initialize account asset state for the issuer and investor.
    issuer_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;
    investor1_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // Mint the asset to the issuer's account.
    issuer_acct.mint_asset(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        asset_id,
        1000,
    )?;

    // Create a settlement to transfer some assets from the issuer to the investor.
    let settlement = SettlementBuilder::new(b"Test")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset,
            amount: 500,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;
    // Submit the settlement.
    let settlement_id = issuer.create_settlement(&mut chain, settlement)?;
    let leg_ref = LegRef::new(settlement_id.into(), 0);

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // The issuer affirms the settlement as the sender.
    issuer_acct.sender_affirmation(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        &leg_ref,
        asset_id,
        500,
    )?;

    // End the block to finalize the new accounts.
    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    // The issuer tries to affirm the settlement as the receiver, which should fail.
    let leg_enc = chain.get_settlement_leg(&leg_ref)?.enc.clone();
    let leg_enc_rand = issuer_acct.decrypt_leg_randomness(&chain, &leg_ref, LegRole::Sender)?;

    // Get the issuer's account state for the asset.
    let mut asset_state = issuer_acct.get_account_asset_state(asset_id)?;

    let proof = ReceiverAffirmationProof::new(
        &mut rng,
        &leg_ref,
        &leg_enc,
        &leg_enc_rand,
        &mut asset_state,
        account_tree.prover_account_tree(),
    )?;
    // This should fail because the issuer is not the receiver.
    let result = chain.receiver_affirmation(&issuer_acct.address(), proof);
    assert!(
        result.is_err(),
        "Sender should not be able to affirm as receiver"
    );

    Ok(())
}
