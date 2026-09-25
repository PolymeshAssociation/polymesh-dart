//! Mirror of the Polymesh `dart-v1` worker protocol's `VerifyDartAssetRequest` and its
//! `_verify` dispatcher.
//!
//! Every variant here maps 1:1 (same order, same field types, same SCALE encoding) to
//! `Polymesh/worker/protocol/dart-v1/src/verify.rs` so that a corpus produced or found by this
//! harness is byte-compatible with what the pallet hands to the worker / runtime fallback.
//!
//! **Keep this in sync with the Polymesh repo** when the protocol enum changes.

use codec::{Decode, Encode};
use rand_chacha::ChaCha20Rng as Rng;
use rand_core::SeedableRng;

use polymesh_dart::curve_tree::{
    AccountTreeConfig, AssetTreeConfig, CompressedCurveTreeRoot, FeeAccountTreeConfig,
    get_account_curve_tree_parameters,
};
use polymesh_dart::key_distribution_proof::KeyDistributionProof;
use polymesh_dart::{
    ACCOUNT_TREE_L, ACCOUNT_TREE_M, ASSET_TREE_L, ASSET_TREE_M, AccountPublicKey,
    AccountRegistrationProof, AssetKeysLookup, AssetMintingProof, AssetPkTLookup,
    BatchedAccountAssetRegistrationProof, BatchedFeeAccountRegistrationProof,
    BatchedFeeAccountTopupProof, EncryptionKeyRegistrationProof, Error as DartError,
    FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountPaymentProof, FeeAccountRegistrationProof,
    FeeAccountTopupProof, InstantReceiverAffirmationProof, InstantSenderAffirmationProof,
    LegEncrypted, MediatorAffirmationProof, PolymeshLimits, ProofHash, ReceiverAffirmationProof,
    ReceiverClaimProof, ReceiverRevertAffirmationProof, SenderAffirmationProof,
    SenderCounterUpdateProof, SenderRevertAffirmationProof, SettlementProof, blake2_256,
};

/// Identity (`polymesh_primitives::IdentityId`) as it is passed to the worker.
pub type Did = [u8; 32];
/// The 32-byte seed the worker derives from the request for its deterministic RNG.
pub type WorkSeed = [u8; 32];

pub type AssetTreeRoot = CompressedCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>;
pub type AccountTreeRoot =
    CompressedCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>;
pub type FeeAccountTreeRoot =
    CompressedCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>;

/// Verify DART asset proof request (mirror of the Polymesh worker protocol type).
#[derive(Encode, Decode, Clone, Debug)]
pub enum VerifyDartAssetRequest {
    AccountRegistration {
        did: Did,
        proof: AccountRegistrationProof<PolymeshLimits>,
    },
    EncryptionKeyRegistration {
        did: Did,
        proof: EncryptionKeyRegistrationProof<PolymeshLimits>,
    },
    BatchedAccountAssetRegistration {
        did: Did,
        asset_lookup: AssetPkTLookup,
        proof: BatchedAccountAssetRegistrationProof<PolymeshLimits>,
    },
    MintAsset {
        did: Did,
        root: AccountTreeRoot,
        proof: AssetMintingProof<PolymeshLimits>,
    },
    CreateSettlement {
        root: AssetTreeRoot,
        asset_lookup: AssetKeysLookup,
        proof: SettlementProof<PolymeshLimits>,
    },
    SenderAffirmation {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: SenderAffirmationProof<PolymeshLimits>,
    },
    ReceiverAffirmation {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: ReceiverAffirmationProof<PolymeshLimits>,
    },
    MediatorAffirmation {
        leg_enc: LegEncrypted,
        mediator: Option<AccountPublicKey>,
        proof: MediatorAffirmationProof<PolymeshLimits>,
    },
    SenderCounterUpdate {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: SenderCounterUpdateProof<PolymeshLimits>,
    },
    SenderRevertAffirmation {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: SenderRevertAffirmationProof<PolymeshLimits>,
    },
    ReceiverRevertAffirmation {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: ReceiverRevertAffirmationProof<PolymeshLimits>,
    },
    ReceiverClaim {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: ReceiverClaimProof<PolymeshLimits>,
    },
    FeeAccountRegistration {
        did: Did,
        proof: FeeAccountRegistrationProof<PolymeshLimits>,
    },
    BatchedFeeAccountRegistration {
        did: Did,
        proof: BatchedFeeAccountRegistrationProof<PolymeshLimits>,
    },
    FeeAccountTopup {
        did: Did,
        root: FeeAccountTreeRoot,
        proof: FeeAccountTopupProof<PolymeshLimits>,
    },
    BatchedFeeAccountTopup {
        did: Did,
        root: FeeAccountTreeRoot,
        proof: BatchedFeeAccountTopupProof<PolymeshLimits>,
    },
    FeeAccountPayment {
        ctx: ProofHash,
        root: FeeAccountTreeRoot,
        proof: FeeAccountPaymentProof<PolymeshLimits>,
    },
    InstantSenderAffirmation {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: InstantSenderAffirmationProof<PolymeshLimits>,
    },
    InstantReceiverAffirmation {
        leg_enc: LegEncrypted,
        root: AccountTreeRoot,
        proof: InstantReceiverAffirmationProof<PolymeshLimits>,
    },
    KeyDistribution {
        did: Did,
        proof: KeyDistributionProof<PolymeshLimits>,
    },
}

impl VerifyDartAssetRequest {
    /// Short stable name of the variant (used for corpus file names and test labels).
    pub fn name(&self) -> &'static str {
        match self {
            Self::AccountRegistration { .. } => "account_registration",
            Self::EncryptionKeyRegistration { .. } => "encryption_key_registration",
            Self::BatchedAccountAssetRegistration { .. } => "batched_account_asset_registration",
            Self::MintAsset { .. } => "mint_asset",
            Self::CreateSettlement { .. } => "create_settlement",
            Self::SenderAffirmation { .. } => "sender_affirmation",
            Self::ReceiverAffirmation { .. } => "receiver_affirmation",
            Self::MediatorAffirmation { .. } => "mediator_affirmation",
            Self::SenderCounterUpdate { .. } => "sender_counter_update",
            Self::SenderRevertAffirmation { .. } => "sender_revert_affirmation",
            Self::ReceiverRevertAffirmation { .. } => "receiver_revert_affirmation",
            Self::ReceiverClaim { .. } => "receiver_claim",
            Self::FeeAccountRegistration { .. } => "fee_account_registration",
            Self::BatchedFeeAccountRegistration { .. } => "batched_fee_account_registration",
            Self::FeeAccountTopup { .. } => "fee_account_topup",
            Self::BatchedFeeAccountTopup { .. } => "batched_fee_account_topup",
            Self::FeeAccountPayment { .. } => "fee_account_payment",
            Self::InstantSenderAffirmation { .. } => "instant_sender_affirmation",
            Self::InstantReceiverAffirmation { .. } => "instant_receiver_affirmation",
            Self::KeyDistribution { .. } => "key_distribution",
        }
    }

    /// Same as the worker: the RNG seed is the blake2-256 of the SCALE-encoded request.
    pub fn work_seed(&self) -> WorkSeed {
        blake2_256(self)
    }

    /// Mirror of `VerifyDartAssetRequest::do_verify` / `_verify` in the Polymesh worker
    /// protocol. Must never panic for any decodable request; returns `Err` on invalid input.
    pub fn verify(&self) -> Result<(), DartError> {
        self.verify_with_seed(self.work_seed())
    }

    /// Mirror of `VerifyDartAssetRequest::_verify`.
    pub fn verify_with_seed(&self, seed: WorkSeed) -> Result<(), DartError> {
        match self {
            Self::AccountRegistration { did, proof } => {
                proof.verify(did)?;
            }
            Self::EncryptionKeyRegistration { did, proof } => {
                proof.verify(did)?;
            }
            Self::BatchedAccountAssetRegistration {
                did,
                proof,
                asset_lookup,
            } => {
                let mut rng = Rng::from_seed(seed);
                let params = get_account_curve_tree_parameters();
                proof.batched_verify(did, params, &mut rng, asset_lookup)?;
            }
            Self::MintAsset { did, root, proof } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(did, root, &mut rng)?;
            }
            Self::CreateSettlement {
                root,
                asset_lookup,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.batched_verify(root, asset_lookup, &mut rng)?;
            }
            Self::SenderAffirmation {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::ReceiverAffirmation {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::InstantSenderAffirmation {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::InstantReceiverAffirmation {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::MediatorAffirmation {
                leg_enc,
                mediator: None,
                proof,
            } => {
                let med_enc = leg_enc.mediator_encryption(proof.key_index)?;
                proof.verify(&med_enc)?;
            }
            Self::MediatorAffirmation {
                leg_enc: _,
                mediator: Some(mediator),
                proof,
            } => {
                proof.verify_revealed(mediator)?;
            }
            Self::SenderCounterUpdate {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::SenderRevertAffirmation {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::ReceiverRevertAffirmation {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::ReceiverClaim {
                leg_enc,
                root,
                proof,
            } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(leg_enc, root, &mut rng)?;
            }
            Self::FeeAccountRegistration { did, proof } => {
                proof.verify(did)?;
            }
            Self::BatchedFeeAccountRegistration { did, proof } => {
                proof.verify(did)?;
            }
            Self::FeeAccountTopup { did, root, proof } => {
                let mut rng = Rng::from_seed(seed);
                // NOTE: `FeeAccountTopupProof::verify` now takes the compressed root (so the
                // tree height is known); Polymesh's `dart-v1` dispatcher must drop its
                // `root.root_node()?` call when it picks up this version.
                proof.verify(&mut rng, did, root)?;
            }
            Self::BatchedFeeAccountTopup { did, root, proof } => {
                let mut rng = Rng::from_seed(seed);
                proof.batched_verify(&mut rng, did, root)?;
            }
            Self::FeeAccountPayment { ctx, root, proof } => {
                let mut rng = Rng::from_seed(seed);
                proof.verify(&mut rng, &ctx.0, root)?;
            }
            Self::KeyDistribution { did, proof } => {
                let mut rng = Rng::from_seed(seed);
                let params = get_account_curve_tree_parameters();
                proof.verify(did, params, &mut rng)?;
            }
        }
        Ok(())
    }

    /// Mirror of `VerifyDartAssetRequest::get_response`: the accessors the pallet calls on a
    /// verified request. These must not panic either (they run after `verify` succeeds, but we
    /// exercise them on arbitrary decodable input too).
    pub fn touch_response_fields(&self) {
        match self {
            Self::AccountRegistration { proof, .. } => {
                let _ = proof.accounts.len();
            }
            Self::EncryptionKeyRegistration { proof, .. } => {
                let _ = proof.keys.len();
            }
            Self::BatchedAccountAssetRegistration { proof, .. } => {
                for state in proof.proofs.iter() {
                    let _ = (
                        state.account,
                        state.asset_id,
                        state.counter,
                        state.account_state_commitment,
                    );
                }
            }
            Self::MintAsset { proof, .. } => {
                let _ = (proof.pk, proof.asset_id, proof.amount, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::CreateSettlement { proof, .. } => {
                let _ = proof.settlement_ref();
                let _: Vec<LegEncrypted> =
                    proof.legs.iter().map(|leg| leg.leg_enc().clone()).collect();
                let _ = proof.revealed_asset_ids();
            }
            Self::SenderAffirmation { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::ReceiverAffirmation { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::InstantSenderAffirmation { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::InstantReceiverAffirmation { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::MediatorAffirmation { proof, .. } => {
                let _ = (proof.leg_ref, proof.accept, proof.is_asset_id_revealed());
            }
            Self::SenderCounterUpdate { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::SenderRevertAffirmation { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::ReceiverRevertAffirmation { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::ReceiverClaim { proof, .. } => {
                let _ = (proof.leg_ref, proof.nullifier);
                let _ = polymesh_dart::AccountStateUpdate::account_state_commitment(proof);
            }
            Self::FeeAccountRegistration { proof, .. } => {
                let _ = (
                    proof.account,
                    proof.asset_id,
                    proof.amount,
                    proof.account_state_commitment,
                );
            }
            Self::BatchedFeeAccountRegistration { proof, .. } => {
                for p in proof.proofs.iter() {
                    let _ = (p.account, p.asset_id, p.amount, p.account_state_commitment);
                }
                let _ = proof.total_amount(0);
            }
            Self::FeeAccountTopup { proof, .. } => {
                let _ = (
                    proof.account,
                    proof.asset_id,
                    proof.amount,
                    proof.updated_account_state_commitment,
                    proof.nullifier,
                );
            }
            Self::BatchedFeeAccountTopup { proof, .. } => {
                for p in proof.proofs.iter() {
                    let _ = (
                        p.account,
                        p.asset_id,
                        p.amount,
                        p.updated_account_state_commitment,
                        p.nullifier,
                    );
                }
            }
            Self::FeeAccountPayment { proof, .. } => {
                let _ = (
                    proof.asset_id,
                    proof.amount,
                    proof.updated_account_state_commitment,
                    proof.nullifier,
                );
            }
            Self::KeyDistribution { proof, .. } => {
                let _ = proof.public_key;
                let _: Vec<_> = proof.recipient_pks.iter().cloned().collect();
            }
        }
    }
}

/// Decode `bytes` as a request and verify it. This is the single function every fuzz target
/// and property test funnels through; it must never panic.
///
/// Returns `None` when the bytes do not SCALE-decode, otherwise the verification result.
pub fn decode_and_verify(bytes: &[u8]) -> Option<Result<(), DartError>> {
    let req = VerifyDartAssetRequest::decode(&mut &bytes[..]).ok()?;
    req.touch_response_fields();
    Some(req.verify())
}
