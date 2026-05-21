use anyhow::Result;
use test_log::test;

use polymesh_dart::*;

mod common;
use common::*;

struct SettlementSetup {
    account_tree: DartProverAccountTree,
    issuer_acct: DartUserAccount,
    investor_acct: DartUserAccount,
    mediator_accts: Option<Vec<DartUserAccount>>,
    asset_id: AssetId,
    settlement: SettlementProof<()>,
    leg_ref: LegRef,
    leg_enc: LegEncrypted,
    amount: Balance,
}

/// Build a minimal chain with a configurable number of mediators, mint assets to the
/// issuer, and produce an un-submitted `SettlementProof`.
fn setup_settlement(num_mediators: usize) -> Result<SettlementSetup> {
    let mut rng = rand::thread_rng();

    let mut chain = DartChainState::new()?;
    let mut account_tree = DartProverAccountTree::new()?;
    account_tree.apply_updates(&chain)?;

    let mut signer_names = vec!["Issuer".to_string()];
    for idx in 0..num_mediators {
        signer_names.push(format!("Mediator{}", idx + 1));
    }
    signer_names.push("Investor".to_string());
    let signer_name_refs: Vec<&str> = signer_names.iter().map(String::as_str).collect();

    let users = chain.create_signers(&signer_name_refs)?;
    let mut issuer = DartUser::new(&users[0]);
    let mut mediator_users = users[1..1 + num_mediators]
        .iter()
        .map(DartUser::new)
        .collect::<Vec<_>>();
    let mut investor = DartUser::new(&users[1 + num_mediators]);

    let issuer_acct = issuer.create_and_register_account(&mut rng, &mut chain, "1")?;
    let mediator_accts = mediator_users
        .iter_mut()
        .enumerate()
        .map(|(idx, mediator)| {
            mediator.create_and_register_account(&mut rng, &mut chain, &(idx + 1).to_string())
        })
        .collect::<Result<Vec<_>>>()?;
    let investor_acct = investor.create_and_register_account(&mut rng, &mut chain, "1")?;

    let mediator_keys = mediator_accts
        .iter()
        .map(|acct| {
            let keys = acct.public_keys();
            (keys.acct, keys.enc)
        })
        .collect::<Vec<_>>();
    let asset_id = issuer.create_asset(&mut chain, &mediator_keys, &[])?;
    let asset = chain.get_asset_state(asset_id)?;

    issuer_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;
    investor_acct.initialize_asset(&mut rng, &mut chain, asset_id)?;

    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    let amount: Balance = 500;
    issuer_acct.mint_asset(
        &mut rng,
        &mut chain,
        account_tree.prover_account_tree(),
        asset_id,
        1000,
    )?;

    chain.end_block()?;
    account_tree.apply_updates(&chain)?;

    let settlement = SettlementBuilder::new(b"LegWrapperTest")
        .leg(LegBuilder {
            sender: issuer_acct.public_keys(),
            receiver: investor_acct.public_keys(),
            asset,
            amount,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, chain.asset_tree())?;

    let settlement_ref = settlement.settlement_ref();
    let leg_ref = LegRef::new(settlement_ref, 0);
    let leg_enc = settlement.legs[0].leg_enc().clone();

    Ok(SettlementSetup {
        account_tree,
        issuer_acct,
        investor_acct,
        mediator_accts: (!mediator_accts.is_empty()).then_some(mediator_accts),
        asset_id,
        settlement,
        leg_ref,
        leg_enc,
        amount,
    })
}

fn build_instant_proof(
    rng: &mut rand::rngs::ThreadRng,
    s: &SettlementSetup,
) -> Result<InstantSettlementProof<()>> {
    let sender = s.issuer_acct.instant_sender_affirmation_proof(
        rng,
        &s.leg_enc,
        s.account_tree.prover_account_tree(),
        &s.leg_ref,
        s.asset_id,
        s.amount,
    )?;
    let receiver = s.investor_acct.instant_receiver_affirmation_proof(
        rng,
        &s.leg_enc,
        s.account_tree.prover_account_tree(),
        &s.leg_ref,
        s.asset_id,
        s.amount,
    )?;
    let mediators = s
        .mediator_accts
        .as_ref()
        .map(|accts| {
            accts
                .iter()
                .enumerate()
                .map(|(idx, acct)| {
                    let med_enc = s.leg_enc.mediator_encryption(idx as MediatorId)?;
                    let mediator_keys = acct.keys();
                    MediatorAffirmationProof::new(
                        rng,
                        &s.leg_ref,
                        &med_enc,
                        &mediator_keys,
                        idx as MediatorId,
                        true,
                    )
                })
                .collect::<core::result::Result<Vec<_>, _>>()
        })
        .transpose()?
        .unwrap_or_default();

    Ok(InstantSettlementProof {
        settlement: s.settlement.clone(),
        leg_affirmations: vec![InstantSettlementLegAffirmations {
            sender,
            receiver,
            mediators: mediators.try_into().expect("Invalid mediator count"),
        }]
        .try_into()
        .expect("Invalid leg count"),
    })
}

fn build_batched_proof(
    rng: &mut rand::rngs::ThreadRng,
    s: &SettlementSetup,
) -> Result<BatchedSettlementProof<()>> {
    let keys = s.issuer_acct.keys();
    let mut sender_state = s.issuer_acct.get_account_asset_state(s.asset_id)?;
    let sender = SenderAffirmationProof::new(
        rng,
        &keys,
        &s.leg_ref,
        s.amount,
        &s.leg_enc,
        &mut sender_state,
        s.account_tree.prover_account_tree(),
    )?;

    let recv_keys = s.investor_acct.keys();
    let mut recv_state = s.investor_acct.get_account_asset_state(s.asset_id)?;
    let receiver = ReceiverAffirmationProof::new(
        rng,
        &recv_keys,
        &s.leg_ref,
        &s.leg_enc,
        &mut recv_state,
        s.account_tree.prover_account_tree(),
    )?;

    Ok(BatchedSettlementProof {
        settlement: s.settlement.clone(),
        leg_affirmations: vec![BatchedSettlementLegAffirmations {
            sender: Some(sender),
            receiver: Some(receiver),
        }]
        .try_into()
        .expect("Invalid leg count"),
    })
}

#[test]
fn test_leg_wrapper_count_leg_affirmations() -> Result<()> {
    // Check `count_leg_affirmations` for instant and batched wrappers across the same scenarios.
    let mut rng = rand::thread_rng();

    let s = setup_settlement(0)?;
    let instant_proof = build_instant_proof(&mut rng, &s)?;
    let counts = instant_proof.count_leg_affirmations();
    assert_eq!(counts.leg_count, 1);
    assert_eq!(counts.sender_count, 1);
    assert_eq!(counts.receiver_count, 1);
    assert_eq!(counts.mediator_count, 0);

    let s = setup_settlement(1)?;
    let instant_proof = build_instant_proof(&mut rng, &s)?;
    let counts = instant_proof.count_leg_affirmations();
    assert_eq!(counts.leg_count, 1);
    assert_eq!(counts.sender_count, 1);
    assert_eq!(counts.receiver_count, 1);
    assert_eq!(counts.mediator_count, 1);

    let s = setup_settlement(0)?;
    let batched_proof = build_batched_proof(&mut rng, &s)?;
    let counts = batched_proof.count_leg_affirmations();
    assert_eq!(counts.leg_count, 1);
    assert_eq!(counts.sender_count, 1);
    assert_eq!(counts.receiver_count, 1);
    assert_eq!(counts.mediator_count, 0);

    let s = setup_settlement(0)?;
    let mut batched_proof = build_batched_proof(&mut rng, &s)?;
    batched_proof.leg_affirmations[0].receiver = None;
    let counts = batched_proof.count_leg_affirmations();
    assert_eq!(counts.leg_count, 1);
    assert_eq!(counts.sender_count, 1);
    assert_eq!(counts.receiver_count, 0);
    assert_eq!(counts.mediator_count, 0);

    let s = setup_settlement(0)?;
    let mut batched_proof = build_batched_proof(&mut rng, &s)?;
    batched_proof.leg_affirmations[0].sender = None;
    batched_proof.leg_affirmations[0].receiver = None;
    let counts = batched_proof.count_leg_affirmations();
    assert_eq!(counts.leg_count, 1);
    assert_eq!(counts.sender_count, 0);
    assert_eq!(counts.receiver_count, 0);
    assert_eq!(counts.mediator_count, 0);

    Ok(())
}

#[test]
fn test_leg_wrapper_check_leg_references() -> Result<()> {
    // Check `check_leg_references` for instant and batched wrappers, including every false branch.
    let mut rng = rand::thread_rng();

    let s = setup_settlement(0)?;
    let instant_proof = build_instant_proof(&mut rng, &s)?;
    assert!(instant_proof.check_leg_references());

    let s = setup_settlement(0)?;
    let mut instant_proof = build_instant_proof(&mut rng, &s)?;
    let dup = instant_proof.leg_affirmations[0].clone();
    instant_proof
        .leg_affirmations
        .try_push(dup)
        .expect("BoundedVec full");
    assert!(!instant_proof.check_leg_references());

    let s_ref = [0u8; 32];
    let s = setup_settlement(0)?;
    let mut instant_proof = build_instant_proof(&mut rng, &s)?;
    instant_proof.leg_affirmations[0].sender.leg_ref = LegRef::new(SettlementRef(s_ref), 0);
    assert!(!instant_proof.check_leg_references());

    let s = setup_settlement(0)?;
    let mut instant_proof = build_instant_proof(&mut rng, &s)?;
    instant_proof.leg_affirmations[0].receiver.leg_ref = LegRef::new(SettlementRef(s_ref), 0);
    assert!(!instant_proof.check_leg_references());

    let s = setup_settlement(1)?;
    let mut instant_proof = build_instant_proof(&mut rng, &s)?;
    instant_proof.leg_affirmations[0].mediators = Default::default();
    assert!(!instant_proof.check_leg_references());

    let s = setup_settlement(1)?;
    let mut instant_proof = build_instant_proof(&mut rng, &s)?;
    instant_proof.leg_affirmations[0].mediators[0].leg_ref = LegRef::new(SettlementRef(s_ref), 0);
    assert!(!instant_proof.check_leg_references());

    let s = setup_settlement(0)?;
    let batched_proof = build_batched_proof(&mut rng, &s)?;
    assert!(batched_proof.check_leg_references());

    let s = setup_settlement(0)?;
    let mut batched_proof = build_batched_proof(&mut rng, &s)?;
    batched_proof.leg_affirmations[0]
        .sender
        .as_mut()
        .unwrap()
        .leg_ref = LegRef::new(SettlementRef(s_ref), 0);
    assert!(!batched_proof.check_leg_references());

    let s = setup_settlement(0)?;
    let mut batched_proof = build_batched_proof(&mut rng, &s)?;
    batched_proof.leg_affirmations[0]
        .receiver
        .as_mut()
        .unwrap()
        .leg_ref = LegRef::new(SettlementRef(s_ref), 0);
    assert!(!batched_proof.check_leg_references());

    Ok(())
}
