use anyhow::Result;
use test_log::test;

use dart::*;

mod common;
use common::*;

#[test]
fn test_minting_asset() -> Result<()> {
    let mut rng = rand::thread_rng();

    // Setup chain state.
    let mut chain = DartChainState::new()?;

    // Create some users.
    let users = chain.create_signers(&["AssetIssuer", "Mediator", "Investor1"])?;
    let issuer = &users[0];
    let mediator = &users[1];
    let investor1 = &users[2];

    // Generate account keys for the issuer, mediator, and investor.
    let issuer_keys = AccountKeys::rand(&mut rng);
    let mediator_keys = AccountKeys::rand(&mut rng);
    let investor1_keys = AccountKeys::rand(&mut rng);

    // Register accounts for the issuer, mediator, and investor.
    chain.register_account(issuer, issuer_keys.public_keys())?;
    chain.register_account(mediator, mediator_keys.public_keys())?;
    chain.register_account(investor1, investor1_keys.public_keys())?;

    let asset_mediator = AuditorOrMediator::mediator(&mediator_keys.public_keys());
    // Create a Dart asset with the issuer as the owner and the mediator as the auditor.
    let asset_details = chain.create_dart_asset(issuer, asset_mediator)?;
    let asset_id = asset_details.asset_id;

    // Initialize account asset state for the issuer and investor.
    let (proof, mut issuer_account) =
        AccountAssetRegistrationProof::new(&mut rng, &issuer_keys, asset_id, issuer.ctx());
    chain.initialize_account_asset(issuer, proof)?;
    issuer_account.commit_pending_state();
    let (proof, mut investor1_account) =
        AccountAssetRegistrationProof::new(&mut rng, &investor1_keys, asset_id, investor1.ctx());
    chain.initialize_account_asset(investor1, proof)?;
    investor1_account.commit_pending_state();

    chain.push_tree_roots();

    // Mint the asset to the issuer's account.
    let proof = AssetMintingProof::new(
        &mut rng,
        &mut issuer_account,
        chain.prover_account_tree(),
        1000,
    )?;
    chain.mint_assets(issuer, proof)?;
    issuer_account.commit_pending_state();

    chain.push_tree_roots();

    // Create a settlement to transfer some assets from the issuer to the investor.
    let settlement = SettlementBuilder::new(b"Test")
        .leg(LegBuilder {
            sender: issuer_keys.public_keys(),
            receiver: investor1_keys.public_keys(),
            asset_id,
            amount: 500,
            mediator: asset_mediator,
        })
        .encryt_and_prove(&mut rng, chain.asset_tree())?;
    // Submit the settlement.
    let settlement_id = chain.create_settlement(issuer, settlement)?;
    let leg_ref = LegRef::new(settlement_id.into(), 0);
    let leg_enc = chain.get_settlement_leg(&leg_ref)?.enc.clone();

    // The issuer affirms the settlement as the sender.
    log::info!("Sender decrypts the leg");
    let sk_e = leg_enc.decrypt_sk_e(LegRole::Sender, &issuer_keys.enc);
    let leg = leg_enc.decrypt(LegRole::Sender, &issuer_keys.enc);
    log::info!("Leg: {:?}", leg);
    log::info!("Sender generate affirmation proof");
    let proof = SenderAffirmationProof::new(
        &mut rng,
        leg_ref.clone(),
        500,
        sk_e,
        &leg_enc,
        &mut issuer_account,
        chain.prover_account_tree(),
    );
    log::info!("Sender affirms");
    chain.sender_affirmation(issuer, proof)?;
    issuer_account.commit_pending_state();

    chain.push_tree_roots();

    // The investor affirms the settlement as the receiver.
    log::info!("Receiver decrypts the leg");
    let sk_e = leg_enc.decrypt_sk_e(LegRole::Receiver, &investor1_keys.enc);
    let leg = leg_enc.decrypt(LegRole::Receiver, &investor1_keys.enc);
    log::info!("Leg: {:?}", leg);
    log::info!("Receiver generate affirmation proof");
    let proof = ReceiverAffirmationProof::new(
        &mut rng,
        leg_ref.clone(),
        sk_e,
        &leg_enc,
        &mut investor1_account,
        chain.prover_account_tree(),
    );
    log::info!("Receiver affirms");
    chain.receiver_affirmation(investor1, proof)?;
    investor1_account.commit_pending_state();

    chain.push_tree_roots();

    // The mediator affirms the settlement.
    log::info!("Mediator decrypts the leg");
    let sk_e = leg_enc.decrypt_sk_e(LegRole::Mediator, &mediator_keys.enc);
    let leg = leg_enc.decrypt(LegRole::Mediator, &mediator_keys.enc);
    log::info!("Leg: {:?}", leg);
    log::info!("Mediator generate affirmation proof");
    let proof = MediatorAffirmationProof::new(
        &mut rng,
        leg_ref.clone(),
        sk_e,
        &leg_enc,
        &mediator_keys.acct,
        true,
    );
    log::info!("Mediator affirms");
    chain.mediator_affirmation(mediator, proof)?;

    // The settlement should have executed.

    chain.push_tree_roots();

    // Receiver claims their assets.
    log::info!("Receiver decrypts the leg for claim");
    let sk_e = leg_enc.decrypt_sk_e(LegRole::Receiver, &investor1_keys.enc);
    let leg = leg_enc.decrypt(LegRole::Receiver, &investor1_keys.enc);
    log::info!("Leg for claim: {:?}", leg);
    log::info!("Receiver generate claim proof");
    let proof = ReceiverClaimProof::new(
        &mut rng,
        leg_ref.clone(),
        500,
        sk_e,
        &leg_enc,
        &mut investor1_account,
        chain.prover_account_tree(),
    );
    log::info!("Receiver claims");
    chain.receiver_claim(investor1, proof)?;
    investor1_account.commit_pending_state();

    Ok(())
}
