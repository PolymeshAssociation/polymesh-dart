use std::time::Instant;
use test_log::test;

use polymesh_dart::*;

mod common;
use common::*;

#[test]
fn test_sender_affirmation_verify() {
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

    let settlement = SettlementBuilder::new(b"Test")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor1_acct.public_keys(),
            asset,
            amount: 500,
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())
        .unwrap();

    let settlement_id = issuer
        .create_settlement(&mut chain, settlement.clone())
        .unwrap();
    let leg_ref = LegRef::new(settlement_id.into(), 0);

    chain.end_block().unwrap();
    account_tree.apply_updates(&chain).unwrap();

    let leg_enc = settlement.legs[0].leg_enc.clone();
    let (_, leg_enc_rand) = leg_enc
        .decrypt_with_randomness(LegRole::sender(), &issuer_acct.keys())
        .unwrap();
    let mut issuer_asset_state = issuer_acct.get_account_asset_state(asset_id).unwrap();

    let proof = SenderAffirmationProof::new(
        &mut rng,
        &issuer_acct.keys().acct,
        &leg_ref,
        500,
        &leg_enc,
        &leg_enc_rand,
        &mut issuer_asset_state,
        account_tree.prover_account_tree(),
    )
    .unwrap();

    let start = Instant::now();
    proof
        .verify(&leg_enc, chain.account_tree(), &mut rng)
        .unwrap();

    println!(
        "For L={ACCOUNT_TREE_L}, height={ACCOUNT_TREE_HEIGHT}, verification time: {:?}",
        start.elapsed()
    );
}
