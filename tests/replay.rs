use test_log::test;

use polymesh_dart::*;

mod common;
use common::*;

#[test]
fn affirmation_rejects_substituted_leg_enc() {
    // An affirmation proof for one leg must not verify against another encrypted leg.
    let mut rng = rand::thread_rng();
    let mut chain = DartChainState::new().unwrap();
    let mut account_tree = DartProverAccountTree::new().unwrap();
    account_tree.apply_updates(&chain).unwrap();
    let users = chain
        .create_signers(&["AssetIssuer", "Investor1", "Investor2"])
        .unwrap();
    let mut issuer = DartUser::new(&users[0]);
    let mut inv1 = DartUser::new(&users[1]);
    let mut inv2 = DartUser::new(&users[2]);
    let issuer_acct = issuer
        .create_and_register_account(&mut rng, &mut chain, "1")
        .unwrap();
    let inv1_acct = inv1
        .create_and_register_account(&mut rng, &mut chain, "1")
        .unwrap();
    let inv2_acct = inv2
        .create_and_register_account(&mut rng, &mut chain, "1")
        .unwrap();
    let asset_id = issuer.create_asset(&mut chain, &[], &[]).unwrap();
    let asset = chain.get_asset_state(asset_id).unwrap();
    issuer_acct
        .initialize_asset(&mut rng, &mut chain, asset_id)
        .unwrap();
    inv1_acct
        .initialize_asset(&mut rng, &mut chain, asset_id)
        .unwrap();
    inv2_acct
        .initialize_asset(&mut rng, &mut chain, asset_id)
        .unwrap();
    chain.end_block().unwrap();
    account_tree.apply_updates(&chain).unwrap();
    issuer_acct
        .mint_asset(
            &mut rng,
            &mut chain,
            account_tree.prover_account_tree(),
            asset_id,
            1000,
        )
        .unwrap();
    // Use two different legs so leg 1 can be substituted for leg 0.
    let settlement = SettlementBuilder::new(b"test")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: inv1_acct.public_keys(),
            asset: asset.clone(),
            amount: 500,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: inv2_acct.public_keys(),
            asset,
            amount: 300,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())
        .unwrap();
    let settlement_id = issuer
        .create_settlement(&mut chain, settlement.clone())
        .unwrap();
    let leg_ref0 = LegRef::new(settlement_id.into(), 0);
    chain.end_block().unwrap();
    account_tree.apply_updates(&chain).unwrap();
    let leg_enc0 = settlement.legs[0].leg_enc().clone();
    let leg_enc1 = settlement.legs[1].leg_enc().clone(); // substituted leg
    assert_ne!(leg_enc0, leg_enc1);
    let mut issuer_state = issuer_acct.get_account_asset_state(asset_id).unwrap();
    // Build the proof for leg 0, then keep the proof and leg_ref fixed.
    let proof = SenderAffirmationProof::<()>::new(
        &mut rng,
        &issuer_acct.keys(),
        &leg_ref0,
        500,
        &leg_enc0,
        &mut issuer_state,
        account_tree.prover_account_tree(),
    )
    .unwrap();
    // Correct leg verifies.
    proof
        .verify(&leg_enc0, chain.account_tree(), &mut rng)
        .unwrap();
    // The same proof must fail with leg 1's encryption.
    assert!(
        proof
            .verify(&leg_enc1, chain.account_tree(), &mut rng)
            .is_err()
    );
}

#[test]
fn affirmation_rejects_substituted_or_repointed_leg() {
    // Check both ways of replaying an affirmation: swapping the encrypted leg or changing leg_ref.
    // A proof should stay bound to both the selected leg slot and that slot's encrypted contents.
    let mut rng = rand::thread_rng();
    let mut chain = DartChainState::new().unwrap();
    let mut account_tree = DartProverAccountTree::new().unwrap();
    account_tree.apply_updates(&chain).unwrap();
    let users = chain.create_signers(&["AssetIssuer", "Investor1"]).unwrap();
    let mut issuer = DartUser::new(&users[0]);
    let mut investor1 = DartUser::new(&users[1]);
    let issuer_acct = issuer
        .create_and_register_account(&mut rng, &mut chain, "1")
        .unwrap();
    let investor1_acct = investor1
        .create_and_register_account(&mut rng, &mut chain, "1")
        .unwrap();
    let asset_id = issuer.create_asset(&mut chain, &[], &[]).unwrap();
    let asset = chain.get_asset_state(asset_id).unwrap();
    issuer_acct
        .initialize_asset(&mut rng, &mut chain, asset_id)
        .unwrap();
    investor1_acct
        .initialize_asset(&mut rng, &mut chain, asset_id)
        .unwrap();
    chain.end_block().unwrap();
    account_tree.apply_updates(&chain).unwrap();
    issuer_acct
        .mint_asset(
            &mut rng,
            &mut chain,
            account_tree.prover_account_tree(),
            asset_id,
            1000,
        )
        .unwrap();
    // Create a second leg to use as the wrong encrypted leg.
    let settlement = SettlementBuilder::new(b"test")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset: asset.clone(),
            amount: 300,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset,
            amount: 200,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())
        .unwrap();
    let settlement_id = issuer
        .create_settlement(&mut chain, settlement.clone())
        .unwrap();
    chain.end_block().unwrap();
    account_tree.apply_updates(&chain).unwrap();
    let leg_ref0 = LegRef::new(settlement_id.into(), 0);
    let leg_enc0 = settlement.legs[0].leg_enc().clone();
    let leg_enc1 = settlement.legs[1].leg_enc().clone();
    let mut issuer_asset_state = issuer_acct.get_account_asset_state(asset_id).unwrap();
    let mut proof = SenderAffirmationProof::<()>::new(
        &mut rng,
        &issuer_acct.keys(),
        &leg_ref0,
        300,
        &leg_enc0,
        &mut issuer_asset_state,
        account_tree.prover_account_tree(),
    )
    .unwrap();
    // Correct leg verifies before trying the replay cases.
    proof
        .verify(&leg_enc0, chain.account_tree(), &mut rng)
        .unwrap();
    // Substituting leg 1's encryption must fail.
    assert!(
        proof
            .verify(&leg_enc1, chain.account_tree(), &mut rng)
            .is_err(),
    );
    // Repointing the proof to slot 1 must also fail.
    proof.leg_ref = LegRef::new(settlement_id.into(), 1);
    assert!(
        proof
            .verify(&leg_enc0, chain.account_tree(), &mut rng)
            .is_err()
    );
}
