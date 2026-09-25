//! Deterministic "world" and one valid request per `VerifyDartAssetRequest` variant.
//!
//! Everything is derived from fixed seeds so the same bytes come out on every run; the encoded
//! requests double as the seed corpus for the coverage-guided fuzzers and as the starting point
//! for the mutation-based property tests.

use std::sync::OnceLock;

use codec::Encode;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;

use polymesh_dart::curve_tree::{
    AccountTreeConfig, AssetTreeConfig, CurveTreeConfig, FeeAccountTreeConfig, ProverCurveTree,
};
use polymesh_dart::key_distribution_proof::KeyDistributionProof;
use polymesh_dart::*;
use polymesh_dart_common::NullifierSkGenCounter;

use crate::request::{Did, VerifyDartAssetRequest};

pub const SEED: [u8; 32] = [0x5a; 32];
pub const DID: Did = [7u8; 32];
pub const ASSET_ID: AssetId = 1;
pub const REVEALED_ASSET_ID: AssetId = 2;
pub const FEE_ASSET: AssetId = FEE_ASSET_ID;
pub const COUNTER: NullifierSkGenCounter = 0;
pub const BALANCE_MINTED: Balance = 1_000;
pub const AMOUNT: Balance = 300;
pub const FEE_BALANCE: Balance = 1_000;
pub const FEE_TOPUP: Balance = 500;
pub const FEE_PAYMENT: Balance = 100;

type AccountProverTree = ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>;
type AssetProverTree = ProverCurveTree<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>;
type FeeProverTree = ProverCurveTree<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>;

pub fn rng() -> ChaCha20Rng {
    ChaCha20Rng::from_seed(SEED)
}

fn keys(seed: &str) -> AccountKeys {
    AccountKeys::from_seed(seed).expect("fixture: keygen")
}

/// A valid request together with the name of its variant.
#[derive(Clone, Debug)]
pub struct Seed {
    pub name: &'static str,
    pub request: VerifyDartAssetRequest,
}

impl Seed {
    pub fn encoded(&self) -> Vec<u8> {
        self.request.encode()
    }
}

/// All valid seed requests. Built once per process (proof generation is slow).
pub fn seeds() -> &'static [Seed] {
    static SEEDS: OnceLock<Vec<Seed>> = OnceLock::new();
    SEEDS.get_or_init(build_seeds)
}

/// A few standalone `LegEncrypted` values (hidden asset-id with auditor+mediator, revealed
/// asset-id, no keys) for the leg-encryption fuzzers.
pub fn leg_encryptions() -> &'static [(&'static str, LegEncrypted)] {
    static LEGS: OnceLock<Vec<(&'static str, LegEncrypted)>> = OnceLock::new();
    LEGS.get_or_init(build_leg_encryptions)
}

fn build_leg_encryptions() -> Vec<(&'static str, LegEncrypted)> {
    let mut rng = rng();
    let alice = keys("fuzz-alice");
    let bob = keys("fuzz-bob");
    let carol = keys("fuzz-carol-mediator");
    let dave = keys("fuzz-dave-auditor");

    let mut out = Vec::new();
    for (name, reveal, visibility, with_keys) in [
        (
            "hidden_full_vis_keys",
            false,
            PartyVisibility::FullVisibility,
            true,
        ),
        (
            "hidden_no_vis_no_keys",
            false,
            PartyVisibility::NoVisibility,
            false,
        ),
        (
            "revealed_full_vis_keys",
            true,
            PartyVisibility::FullVisibility,
            true,
        ),
        (
            "revealed_sender_sees",
            true,
            PartyVisibility::OnlySenderSeesReceiver,
            false,
        ),
    ] {
        let leg = Leg::new(alice.enc.public, bob.enc.public, ASSET_ID, AMOUNT).unwrap();
        let (enc_keys, med_keys, pub_keys) = if with_keys {
            (
                vec![dave.enc.public.get_affine().unwrap()],
                vec![carol.acct.public.get_affine().unwrap()],
                vec![carol.enc.public.get_affine().unwrap()],
            )
        } else {
            (vec![], vec![], vec![])
        };
        let (_, leg_enc, _) = leg
            .encrypt(
                &mut rng,
                LegConfig {
                    visibility,
                    reveal_asset_id: reveal,
                }
                .into(),
                enc_keys,
                med_keys,
                pub_keys,
            )
            .expect("fixture: leg encrypt");
        out.push((name, leg_enc));
    }
    out
}

fn build_seeds() -> Vec<Seed> {
    let mut rng = rng();
    let mut seeds = Vec::new();

    let alice = keys("fuzz-alice"); // issuer / sender
    let bob = keys("fuzz-bob"); // receiver
    let carol = keys("fuzz-carol-mediator");
    let dave = keys("fuzz-dave-auditor");
    let erin = keys("fuzz-erin-fee");

    let tree_params = AccountTreeConfig::parameters();

    // ---- Key registrations -------------------------------------------------------------
    let proof = AccountRegistrationProof::<PolymeshLimits>::new(
        &mut rng,
        &[alice.clone(), bob.clone()],
        &DID,
    )
    .unwrap();
    seeds.push(Seed {
        name: "account_registration",
        request: VerifyDartAssetRequest::AccountRegistration { did: DID, proof },
    });

    let proof = EncryptionKeyRegistrationProof::<PolymeshLimits>::new(
        &mut rng,
        &[dave.enc.clone(), carol.enc.clone()],
        &DID,
    )
    .unwrap();
    seeds.push(Seed {
        name: "encryption_key_registration",
        request: VerifyDartAssetRequest::EncryptionKeyRegistration { did: DID, proof },
    });

    // ---- Account/asset registration (batched, with and without pk_T) -------------------
    let pk_t = EncryptionKeyPair::rand(&mut rng).unwrap();
    let mut pk_t_lookup = AssetPkTLookup::default();
    pk_t_lookup.add(REVEALED_ASSET_ID, pk_t.public);
    let (proof, _states) = BatchedAccountAssetRegistrationProof::<PolymeshLimits>::new(
        &mut rng,
        &[
            (alice.clone(), ASSET_ID, COUNTER, None),
            (bob.clone(), REVEALED_ASSET_ID, COUNTER, Some(pk_t.public)),
        ],
        &DID,
        tree_params,
    )
    .unwrap();
    seeds.push(Seed {
        name: "batched_account_asset_registration",
        request: VerifyDartAssetRequest::BatchedAccountAssetRegistration {
            did: DID,
            asset_lookup: pk_t_lookup,
            proof,
        },
    });

    // ---- Account tree with every leaf the affirmation proofs need ----------------------
    // Alice: sender with balance; Bob: receiver; both also at pending counter 1 for the
    // counter-decreasing proofs (revert / counter-update / claim).
    let (mut alice_state, _) = alice.init_asset_state(ASSET_ID, COUNTER, &DID).unwrap();
    alice_state.current_state.balance = BALANCE_MINTED;
    let (bob_state, _) = bob.init_asset_state(ASSET_ID, COUNTER, &DID).unwrap();
    let mut alice_state_c1 = alice_state.clone();
    alice_state_c1.current_state.counter = 1;
    let mut bob_state_c1 = bob_state.clone();
    bob_state_c1.current_state.counter = 1;
    // Mint uses a fresh (zero-balance) issuer state so it does not collide with the sender leaf.
    let (mut mint_state, _) = alice
        .init_asset_state(REVEALED_ASSET_ID, COUNTER, &DID)
        .unwrap();

    let mut account_tree = AccountProverTree::new(ACCOUNT_TREE_HEIGHT).unwrap();
    for st in [
        &alice_state,
        &bob_state,
        &alice_state_c1,
        &bob_state_c1,
        &mint_state,
    ] {
        let leaf = st.current_commitment().unwrap().as_leaf_value().unwrap();
        account_tree.insert(leaf).unwrap();
    }
    account_tree.store_root().unwrap();
    let account_root = account_tree.root().unwrap();

    // ---- Mint ---------------------------------------------------------------------------
    let proof = AssetMintingProof::<PolymeshLimits>::new(
        &mut rng,
        &alice,
        &DID,
        &mut mint_state,
        &account_tree,
        BALANCE_MINTED,
    )
    .unwrap();
    seeds.push(Seed {
        name: "mint_asset",
        request: VerifyDartAssetRequest::MintAsset {
            did: DID,
            root: account_root.clone(),
            proof,
        },
    });

    // ---- Assets + settlement --------------------------------------------------------------
    let asset_hidden = AssetState::new::<PolymeshLimits>(
        ASSET_ID,
        &[(carol.acct.public, carol.enc.public)],
        &[dave.enc.public],
    )
    .unwrap();
    let asset_revealed = AssetState::new::<PolymeshLimits>(
        REVEALED_ASSET_ID,
        &[(carol.acct.public, carol.enc.public)],
        &[dave.enc.public],
    )
    .unwrap();
    // Asset ids double as leaf indices in the asset tree.
    let asset_zero = AssetState::new::<PolymeshLimits>(0, &[], &[]).unwrap();
    let mut asset_tree = AssetProverTree::new(ASSET_TREE_HEIGHT).unwrap();
    for a in [&asset_zero, &asset_hidden, &asset_revealed] {
        asset_tree.insert(a.commitment().unwrap()).unwrap();
    }
    asset_tree.store_root().unwrap();
    let asset_root = asset_tree.root().unwrap();
    let mut asset_lookup = AssetKeysLookup::new();
    asset_lookup.add(asset_zero.clone());
    asset_lookup.add(asset_hidden.clone());
    asset_lookup.add(asset_revealed.clone());

    let settlement = SettlementBuilder::<PolymeshLimits>::new(b"fuzz-settlement")
        .leg(LegBuilder {
            sender: alice.public_keys(),
            receiver: bob.public_keys(),
            asset: asset_hidden.clone(),
            amount: AMOUNT,
            config: LegConfig {
                reveal_asset_id: false,
                visibility: PartyVisibility::FullVisibility,
            },
            public_enc_keys: vec![erin.enc.public],
        })
        .leg(LegBuilder {
            sender: bob.public_keys(),
            receiver: alice.public_keys(),
            asset: asset_revealed.clone(),
            amount: AMOUNT,
            config: LegConfig {
                reveal_asset_id: true,
                visibility: PartyVisibility::OnlyReceiverSeesSender,
            },
            public_enc_keys: vec![],
        })
        .encrypt_and_prove(&mut rng, &asset_tree)
        .unwrap();
    let settlement_ref = settlement.settlement_ref();
    let leg_enc_hidden = settlement.legs[0].leg_enc().clone();
    let leg_enc_revealed = settlement.legs[1].leg_enc().clone();
    seeds.push(Seed {
        name: "create_settlement",
        request: VerifyDartAssetRequest::CreateSettlement {
            root: asset_root,
            asset_lookup,
            proof: settlement,
        },
    });

    // ---- Affirmations on the hidden-asset leg (leg 0: alice -> bob) --------------------
    let leg_ref = LegRef::new(settlement_ref, 0);

    // `with_balance!` proofs take `(leg_ref, amount, leg_enc)`, `no_balance!` proofs take
    // `(leg_ref, leg_enc, amount)`.
    macro_rules! affirm {
        (balance, $name:literal, $variant:ident, $proof_ty:ident, $keys:expr, $state:expr, $leg:expr) => {{
            let mut state = $state.clone();
            let proof = $proof_ty::<PolymeshLimits>::new(
                &mut rng,
                &$keys,
                &leg_ref,
                AMOUNT,
                &$leg,
                &mut state,
                &account_tree,
            )
            .unwrap();
            seeds.push(Seed {
                name: $name,
                request: VerifyDartAssetRequest::$variant {
                    leg_enc: $leg.clone(),
                    root: account_root.clone(),
                    proof,
                },
            });
        }};
        (no_balance, $name:literal, $variant:ident, $proof_ty:ident, $keys:expr, $state:expr, $leg:expr) => {{
            let mut state = $state.clone();
            let proof = $proof_ty::<PolymeshLimits>::new(
                &mut rng,
                &$keys,
                &leg_ref,
                &$leg,
                AMOUNT,
                &mut state,
                &account_tree,
            )
            .unwrap();
            seeds.push(Seed {
                name: $name,
                request: VerifyDartAssetRequest::$variant {
                    leg_enc: $leg.clone(),
                    root: account_root.clone(),
                    proof,
                },
            });
        }};
    }

    affirm!(
        balance,
        "sender_affirmation",
        SenderAffirmation,
        SenderAffirmationProof,
        alice,
        alice_state,
        leg_enc_hidden
    );
    affirm!(
        no_balance,
        "receiver_affirmation",
        ReceiverAffirmation,
        ReceiverAffirmationProof,
        bob,
        bob_state,
        leg_enc_hidden
    );
    affirm!(
        balance,
        "instant_sender_affirmation",
        InstantSenderAffirmation,
        InstantSenderAffirmationProof,
        alice,
        alice_state,
        leg_enc_hidden
    );
    affirm!(
        balance,
        "instant_receiver_affirmation",
        InstantReceiverAffirmation,
        InstantReceiverAffirmationProof,
        bob,
        bob_state,
        leg_enc_hidden
    );
    affirm!(
        balance,
        "receiver_claim",
        ReceiverClaim,
        ReceiverClaimProof,
        bob,
        bob_state_c1,
        leg_enc_hidden
    );
    affirm!(
        balance,
        "sender_revert_affirmation",
        SenderRevertAffirmation,
        SenderRevertAffirmationProof,
        alice,
        alice_state_c1,
        leg_enc_hidden
    );
    affirm!(
        no_balance,
        "sender_counter_update",
        SenderCounterUpdate,
        SenderCounterUpdateProof,
        alice,
        alice_state_c1,
        leg_enc_hidden
    );
    affirm!(
        no_balance,
        "receiver_revert_affirmation",
        ReceiverRevertAffirmation,
        ReceiverRevertAffirmationProof,
        bob,
        bob_state_c1,
        leg_enc_hidden
    );

    // ---- Mediator affirmations (hidden ring + revealed PoK) -----------------------------
    let med_enc = leg_enc_hidden.mediator_encryption(0).unwrap();
    let proof = MediatorAffirmationProof::<PolymeshLimits>::new(
        &mut rng, &leg_ref, &med_enc, &carol, 0, true,
    )
    .unwrap();
    seeds.push(Seed {
        name: "mediator_affirmation_hidden",
        request: VerifyDartAssetRequest::MediatorAffirmation {
            leg_enc: leg_enc_hidden.clone(),
            mediator: None,
            proof,
        },
    });
    let leg_ref_1 = LegRef::new(settlement_ref, 1);
    let proof = MediatorAffirmationProof::<PolymeshLimits>::new_revealed(
        &mut rng, &leg_ref_1, &carol, 0, false,
    )
    .unwrap();
    seeds.push(Seed {
        name: "mediator_affirmation_revealed",
        request: VerifyDartAssetRequest::MediatorAffirmation {
            leg_enc: leg_enc_revealed.clone(),
            mediator: Some(carol.acct.public),
            proof,
        },
    });

    // ---- Fee accounts -------------------------------------------------------------------
    let (proof, fee_state) = FeeAccountRegistrationProof::<PolymeshLimits>::new(
        &mut rng,
        &erin.acct,
        FEE_ASSET,
        FEE_BALANCE,
        &DID,
    )
    .unwrap();
    seeds.push(Seed {
        name: "fee_account_registration",
        request: VerifyDartAssetRequest::FeeAccountRegistration { did: DID, proof },
    });

    let (proof, _) = BatchedFeeAccountRegistrationProof::<PolymeshLimits>::new(
        &mut rng,
        &[
            (&alice.acct, FEE_ASSET, FEE_BALANCE),
            (&bob.acct, FEE_ASSET, FEE_BALANCE),
        ],
        &DID,
    )
    .unwrap();
    seeds.push(Seed {
        name: "batched_fee_account_registration",
        request: VerifyDartAssetRequest::BatchedFeeAccountRegistration { did: DID, proof },
    });

    let (_, fee_state_a) = FeeAccountRegistrationProof::<PolymeshLimits>::new(
        &mut rng,
        &alice.acct,
        FEE_ASSET,
        FEE_BALANCE,
        &DID,
    )
    .unwrap();
    let (_, fee_state_b) = FeeAccountRegistrationProof::<PolymeshLimits>::new(
        &mut rng,
        &bob.acct,
        FEE_ASSET,
        FEE_BALANCE,
        &DID,
    )
    .unwrap();
    let mut fee_state = fee_state;
    let mut fee_tree = FeeProverTree::new(FEE_ACCOUNT_TREE_HEIGHT).unwrap();
    for st in [&fee_state, &fee_state_a, &fee_state_b] {
        let leaf = st.current_commitment().unwrap().as_leaf_value().unwrap();
        fee_tree.insert(leaf).unwrap();
    }
    fee_tree.store_root().unwrap();
    let fee_root = fee_tree.root().unwrap();

    let proof = FeeAccountTopupProof::<PolymeshLimits>::new(
        &mut rng,
        &erin.acct,
        &mut fee_state.clone(),
        FEE_TOPUP,
        &DID,
        &fee_tree,
    )
    .unwrap();
    seeds.push(Seed {
        name: "fee_account_topup",
        request: VerifyDartAssetRequest::FeeAccountTopup {
            did: DID,
            root: fee_root.clone(),
            proof,
        },
    });

    let mut topups = vec![
        (&alice.acct, FEE_TOPUP, fee_state_a.clone()),
        (&bob.acct, FEE_TOPUP, fee_state_b.clone()),
    ];
    let proof =
        BatchedFeeAccountTopupProof::<PolymeshLimits>::new(&mut rng, &mut topups, &DID, &fee_tree)
            .unwrap();
    seeds.push(Seed {
        name: "batched_fee_account_topup",
        request: VerifyDartAssetRequest::BatchedFeeAccountTopup {
            did: DID,
            root: fee_root.clone(),
            proof,
        },
    });

    let ctx = ProofHash([0x11; 32]);
    let proof = FeeAccountPaymentProof::<PolymeshLimits>::new(
        &mut rng,
        &erin.acct,
        &ctx.0,
        &mut fee_state,
        FEE_PAYMENT,
        &fee_tree,
    )
    .unwrap();
    seeds.push(Seed {
        name: "fee_account_payment",
        request: VerifyDartAssetRequest::FeeAccountPayment {
            ctx,
            root: fee_root,
            proof,
        },
    });

    // ---- Key distribution ---------------------------------------------------------------
    let proof = KeyDistributionProof::<PolymeshLimits>::new(
        &mut rng,
        &dave.enc,
        vec![carol.enc.public, erin.enc.public, alice.enc.public],
        &DID,
        tree_params,
    )
    .unwrap();
    seeds.push(Seed {
        name: "key_distribution",
        request: VerifyDartAssetRequest::KeyDistribution { did: DID, proof },
    });

    // Sanity: every seed must verify.
    for s in &seeds {
        s.request
            .verify()
            .unwrap_or_else(|e| panic!("fixture `{}` must verify: {e:?}", s.name));
    }
    seeds
}
