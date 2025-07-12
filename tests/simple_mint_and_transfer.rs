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

    let asset_mediator = AuditorOrMediator::mediator(&mediator_acct.public_keys());
    // Create a Dart asset with the issuer as the owner and the mediator as the auditor.
    let asset_id = issuer.create_asset(&mut chain, asset_mediator)?;

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
            asset_id,
            amount: 500,
            mediator: asset_mediator,
        })
        .encryt_and_prove(&mut rng, chain.asset_tree())?;
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
    let asset1_auditor = AuditorOrMediator::auditor(&auditor_acct.public_keys().enc);
    let asset2_mediator = AuditorOrMediator::mediator(&mediator_acct.public_keys());

    let asset1_id = issuer1.create_asset(&mut chain, asset1_auditor)?;
    let asset2_id = issuer2.create_asset(&mut chain, asset2_mediator)?;

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
            asset_id: asset1_id,
            amount: 1000,
            mediator: asset1_auditor,
        })
        .encryt_and_prove(&mut rng, chain.asset_tree())?;
    eprintln!("Creating funding settlement: {:?}", funding_settlement1);
    let funding_settlement1_id = issuer1.create_settlement(&mut chain, funding_settlement1)?;
    let funding_leg1_ref = LegRef::new(funding_settlement1_id.into(), 0);

    // Issuer2 sends asset2 to investor2
    let funding_settlement2 = SettlementBuilder::new(b"Funding2")
        .leg(LegBuilder {
            sender: issuer2_acct.public_keys(),
            receiver: investor2_acct.public_keys(),
            asset_id: asset2_id,
            amount: 1500,
            mediator: asset2_mediator,
        })
        .encryt_and_prove(&mut rng, chain.asset_tree())?;
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
            asset_id: asset1_id,
            amount: 500,
            mediator: asset1_auditor,
        })
        .leg(LegBuilder {
            sender: investor2_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset_id: asset2_id,
            amount: 750,
            mediator: asset2_mediator,
        })
        .encryt_and_prove(&mut rng, chain.asset_tree())?;
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
    Ok(())
}
