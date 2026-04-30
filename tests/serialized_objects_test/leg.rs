use polymesh_dart::curve_tree::{AssetTreeConfig, ProverCurveTree};
use polymesh_dart::*;

use crate::constants::*;
use crate::utils::{alice_keys, bob_keys, default_rng, load_scale_v1, save_scale_v1};

fn settlement_proof_file(n_legs: usize, n_aud: usize, n_med: usize, n_pub: usize) -> String {
    format!(
        "{}_{}_legs_{}_aud_{}_med_{}_pub.bin",
        SETTLEMENT_PROOF_PREFIX, n_legs, n_aud, n_med, n_pub
    )
}

type AssetProverTree = ProverCurveTree<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>;

/// Build an asset tree containing the given asset states.
/// Each `AssetState` must have an `asset_id` equal to its insertion order (0, 1, 2, …)
/// because `get_path_to_leaf_index` uses `asset_id` as the leaf index.
fn build_asset_tree(asset_states: &[AssetState]) -> (AssetProverTree, AssetKeysLookup) {
    let mut tree = AssetProverTree::new(ASSET_TREE_HEIGHT).unwrap();
    let mut lookup = AssetKeysLookup::new();
    for state in asset_states {
        tree.insert(state.commitment().unwrap()).unwrap();
        lookup.add(state.clone());
    }
    tree.store_root().unwrap();
    (tree, lookup)
}

pub fn gen_leg_encrypted() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let leg = Leg::new(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_0,
        SETTLEMENT_AMOUNT,
    )
    .unwrap();
    let (_, leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegConfig::default().into(),
            vec![],
            vec![],
            vec![],
        )
        .unwrap();
    save_scale_v1(LEG_ENCRYPTED, &leg_enc);
}

pub fn gen_mediator_encryption() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    // One mediator so mediator_encryption(0) is valid.
    let mediators_config = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &mediators_config, &[]).unwrap();
    let leg = Leg::new(
        sender_keys.enc.public,
        receiver_keys.enc.public,
        ASSET_ID_0,
        SETTLEMENT_AMOUNT,
    )
    .unwrap();
    let (asset_enc_keys, asset_med_keys) = asset_state.get_encryption_and_mediator_keys().unwrap();
    let (_, leg_enc, _) = leg
        .encrypt(
            &mut rng,
            LegConfig::default().into(),
            asset_enc_keys,
            asset_med_keys,
            vec![],
        )
        .unwrap();
    let med_enc = leg_enc.mediator_encryption(0).unwrap();
    save_scale_v1(MEDIATOR_ENCRYPTION, &med_enc);
}

#[test]
fn verify_v1_leg_encrypted() {
    let leg_enc: LegEncrypted = load_scale_v1(LEG_ENCRYPTED);
    leg_enc.decode().unwrap();
}

#[test]
fn verify_v1_mediator_encryption() {
    let med_enc: MediatorEncryption = load_scale_v1(MEDIATOR_ENCRYPTION);
    med_enc.decode().unwrap();
}

/// Verify a settlement proof loaded from disk.
fn verify_settlement(filename: &str, asset_states: &[AssetState]) {
    let mut rng = default_rng();
    let (asset_tree, asset_lookup) = build_asset_tree(asset_states);
    let proof: SettlementProof = load_scale_v1(filename);
    proof
        .verify(asset_tree.root().unwrap(), &asset_lookup, &mut rng)
        .unwrap();
}

pub fn gen_settlement_proof() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    // Asset will be at index 0
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    let (asset_tree, _) = build_asset_tree(&[asset_state.clone()]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(&settlement_proof_file(1, 1, 1, 0), &proof);
}

pub fn gen_settlement_proof_2_legs() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    // Assets will be at leaf indices 0 and 1 respectively
    let asset_state_0 = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    let asset_state_1 = AssetState::new::<()>(ASSET_ID_1, &mediators, &auditors).unwrap();
    let (asset_tree, _) = build_asset_tree(&[asset_state_0.clone(), asset_state_1.clone()]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state_0,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .leg(LegBuilder {
            sender: receiver_keys.public_keys(),
            receiver: sender_keys.public_keys(),
            asset: asset_state_1,
            amount: SETTLEMENT_AMOUNT / 2,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(&settlement_proof_file(2, 1, 1, 0), &proof);
}

pub fn gen_settlement_proof_3_legs() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    let asset_state_0 = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    let asset_state_1 = AssetState::new::<()>(ASSET_ID_1, &mediators, &auditors).unwrap();
    let asset_state_2 = AssetState::new::<()>(ASSET_ID_2, &mediators, &auditors).unwrap();
    let (asset_tree, _) = build_asset_tree(&[
        asset_state_0.clone(),
        asset_state_1.clone(),
        asset_state_2.clone(),
    ]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state_0,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .leg(LegBuilder {
            sender: receiver_keys.public_keys(),
            receiver: sender_keys.public_keys(),
            asset: asset_state_1,
            amount: SETTLEMENT_AMOUNT / 2,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state_2,
            amount: SETTLEMENT_AMOUNT / 3,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(&settlement_proof_file(3, 1, 1, 0), &proof);
}

pub fn gen_settlement_proof_with_auditor() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let auditors = [auditor_enc_key.public];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &auditors).unwrap();
    let (asset_tree, _) = build_asset_tree(&[asset_state.clone()]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(&settlement_proof_file(1, 1, 0, 0), &proof);
}

pub fn gen_settlement_proof_1_aud_1_med_1_pub() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let public_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    let (asset_tree, _) = build_asset_tree(&[asset_state.clone()]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig::default(),
            public_enc_keys: vec![public_enc_key.public],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(&settlement_proof_file(1, 1, 1, 1), &proof);
}

pub fn gen_settlement_proof_revealed_asset_id() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &[]).unwrap();
    let (asset_tree, _) = build_asset_tree(&[asset_state.clone()]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig {
                reveal_asset_id: true,
                parties_see_each_other: true,
            },
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(SETTLEMENT_PROOF_REVEALED_ASSET_ID, &proof);
}

pub fn gen_settlement_proof_parties_hidden() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &[]).unwrap();
    let (asset_tree, _) = build_asset_tree(&[asset_state.clone()]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig {
                reveal_asset_id: false,
                parties_see_each_other: false,
            },
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(SETTLEMENT_PROOF_PARTIES_HIDDEN, &proof);
}

#[test]
fn verify_v1_settlement_proof() {
    let mut rng = default_rng();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    verify_settlement(&settlement_proof_file(1, 1, 1, 0), &[asset_state]);
}

#[test]
fn verify_v1_settlement_proof_2_legs() {
    let mut rng = default_rng();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    let asset_state_0 = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    let asset_state_1 = AssetState::new::<()>(ASSET_ID_1, &mediators, &auditors).unwrap();
    verify_settlement(
        &settlement_proof_file(2, 1, 1, 0),
        &[asset_state_0, asset_state_1],
    );
}

#[test]
fn verify_v1_settlement_proof_with_auditor() {
    let mut rng = default_rng();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let auditors = [auditor_enc_key.public];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &auditors).unwrap();
    verify_settlement(&settlement_proof_file(1, 1, 0, 0), &[asset_state]);
}

#[test]
fn verify_v1_settlement_proof_revealed_asset_id() {
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &[]).unwrap();
    verify_settlement(SETTLEMENT_PROOF_REVEALED_ASSET_ID, &[asset_state]);
}

#[test]
fn verify_v1_settlement_proof_parties_hidden() {
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &[]).unwrap();
    verify_settlement(SETTLEMENT_PROOF_PARTIES_HIDDEN, &[asset_state]);
}

pub fn gen_settlement_proof_2_auditors() {
    let mut rng = default_rng();
    let sender_keys = alice_keys();
    let receiver_keys = bob_keys();
    let auditor_enc_key_0 = EncryptionKeyPair::rand(&mut rng).unwrap();
    let auditor_enc_key_1 = EncryptionKeyPair::rand(&mut rng).unwrap();
    let auditors = [auditor_enc_key_0.public, auditor_enc_key_1.public];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &auditors).unwrap();
    let (asset_tree, _) = build_asset_tree(&[asset_state.clone()]);
    let proof = SettlementBuilder::<()>::new(IDENTITY)
        .leg(LegBuilder {
            sender: sender_keys.public_keys(),
            receiver: receiver_keys.public_keys(),
            asset: asset_state,
            amount: SETTLEMENT_AMOUNT,
            config: LegConfig::default(),
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    save_scale_v1(SETTLEMENT_PROOF_2_AUDITORS, &proof);
}

#[test]
fn verify_v1_settlement_proof_3_legs() {
    let mut rng = default_rng();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    let asset_state_0 = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    let asset_state_1 = AssetState::new::<()>(ASSET_ID_1, &mediators, &auditors).unwrap();
    let asset_state_2 = AssetState::new::<()>(ASSET_ID_2, &mediators, &auditors).unwrap();
    verify_settlement(
        &settlement_proof_file(3, 1, 1, 0),
        &[asset_state_0, asset_state_1, asset_state_2],
    );
}

#[test]
fn verify_v1_settlement_proof_1aud_1med_1pub() {
    let mut rng = default_rng();
    let mediator_keys = AccountKeys::from_seed(CAROL_SEED).unwrap();
    let auditor_enc_key = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mediators = [(mediator_keys.acct.public, mediator_keys.enc.public)];
    let auditors = [auditor_enc_key.public];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &mediators, &auditors).unwrap();
    verify_settlement(&settlement_proof_file(1, 1, 1, 1), &[asset_state]);
}

#[test]
fn verify_v1_settlement_proof_2_auditors() {
    let mut rng = default_rng();
    let auditor_enc_key_0 = EncryptionKeyPair::rand(&mut rng).unwrap();
    let auditor_enc_key_1 = EncryptionKeyPair::rand(&mut rng).unwrap();
    let auditors = [auditor_enc_key_0.public, auditor_enc_key_1.public];
    let asset_state = AssetState::new::<()>(ASSET_ID_0, &[], &auditors).unwrap();
    verify_settlement(SETTLEMENT_PROOF_2_AUDITORS, &[asset_state]);
}
