use codec::{Decode, Encode};
use scale_info::TypeInfo;

use rand_core::{CryptoRng, RngCore};

use ark_ec::CurveConfig;
use bounded_collections::BoundedVec;

use polymesh_dart_bp::account as bp_account;
use polymesh_dart_common::LegId;

use crate::curve_tree::*;
use crate::*;

/// Represents the affirmation proofs for each leg in a settlement.
/// This includes the sender, and receiver affirmation proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct InstantSettlementLegAffirmations<
    T: DartLimits = (),
    C: CurveTreeConfig = AccountTreeConfig,
> {
    /// The sender's affirmation proof.
    pub sender: InstantSenderAffirmationProof<C>,
    /// The receiver's affirmation proof.
    pub receiver: InstantReceiverAffirmationProof<C>,
    /// The mediator affirmation proofs.
    pub mediators: BoundedVec<MediatorAffirmationProof, T::MaxAssetMediators>,
}

/// A batched settlement proof allows including the sender and receiver affirmation proofs
/// with the settlement creation proof to reduce the number of transactions
/// required to finalize a settlement.
#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct InstantSettlementProof<
    T: DartLimits = (),
    C: CurveTreeConfig = AssetTreeConfig,
    A: CurveTreeConfig = AccountTreeConfig,
> {
    /// The settlement proof containing the memo, root, and legs.
    pub settlement: SettlementProof<T, C>,

    /// The leg affirmations for each leg in the settlement.
    pub leg_affirmations: BoundedVec<InstantSettlementLegAffirmations<T, A>, T::MaxSettlementLegs>,
}

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <VestaParameters as CurveConfig>::ScalarField,
            F1 = <PallasParameters as CurveConfig>::ScalarField,
            P0 = VestaParameters,
            P1 = PallasParameters,
        >,
    A: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> InstantSettlementProof<T, C, A>
{
    /// Get leg and sender, receiver and mediator affirmation counts.
    pub fn count_leg_affirmations(&self) -> SettlementCounts {
        let mut leg_count = 0;
        let mut mediator_count = 0;

        for leg_aff in &self.leg_affirmations {
            leg_count += 1;
            mediator_count += leg_aff.mediators.len() as u64;
        }

        SettlementCounts {
            leg_count,
            sender_count: leg_count as u64,
            receiver_count: leg_count as u64,
            mediator_count,
        }
    }

    /// Check leg references in affirmation proofs.
    ///
    /// Returns `true` if all leg references match the settlement legs.
    pub fn check_leg_references(&self) -> bool {
        // Check that the number of legs in the settlement matches the number of leg affirmations.
        if self.settlement.legs.len() != self.leg_affirmations.len() {
            return false;
        }

        let settlement = self.settlement.settlement_ref();
        for (idx, (leg_aff, leg)) in self
            .leg_affirmations
            .iter()
            .zip(&self.settlement.legs)
            .enumerate()
        {
            let leg_ref = LegRef::new(settlement, idx as LegId);
            // Check sender leg reference.
            if leg_aff.sender.leg_ref != leg_ref {
                return false;
            }
            // Check receiver leg reference.
            if leg_aff.receiver.leg_ref != leg_ref {
                return false;
            }
            // Check the mediator count matches the leg's mediator count.
            if let Some(mediator_count) = leg.mediator_count().ok() {
                if mediator_count != leg_aff.mediators.len() {
                    return false;
                }
            } else {
                // Failed to get mediator count.
                return false;
            }
            // Check all mediator leg references.
            for mediator in &leg_aff.mediators {
                if mediator.leg_ref != leg_ref {
                    return false;
                }
            }
        }
        true
    }
}

type BPAffirmAsSenderTxnProof<C> = bp_account::IrreversibleAffirmAsSenderTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The sender affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct InstantSenderAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    inner: WrappedCanonical<BPAffirmAsSenderTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> InstantSenderAffirmationProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the sender affirmation.
        let state_change = account_asset.get_instant_sender_affirm_state(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::IrreversibleAffirmAsSenderTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            inner: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for sender affirmation proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.inner.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for InstantSenderAffirmationProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}

type BPAffirmAsReceiverTxnProof<C> = bp_account::IrreversibleAffirmAsReceiverTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The receiver affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct InstantReceiverAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    inner: WrappedCanonical<BPAffirmAsReceiverTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> InstantReceiverAffirmationProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the receiver affirmation.
        let state_change = account_asset.get_instant_receiver_affirm_state(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::IrreversibleAffirmAsReceiverTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            inner: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for receiver affirmation proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.inner.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for InstantReceiverAffirmationProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}
