use codec::{Decode, Encode};
use scale_info::TypeInfo;

use rand_core::{CryptoRng, RngCore};

use bounded_collections::BoundedVec;

use polymesh_dart_bp::{account as bp_account, leg as bp_leg};
use polymesh_dart_common::{LegId, MediatorId};

use super::WrappedCanonical;
use super::*;

/// Represents the affirmation proofs for each leg in a settlement.
/// This includes the sender, and receiver affirmation proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct BatchedSettlementLegAffirmations<C: CurveTreeConfig = AccountTreeConfig> {
    /// The sender's affirmation proof.
    pub sender: Option<SenderAffirmationProof<C>>,
    /// The receiver's affirmation proof.
    pub receiver: Option<ReceiverAffirmationProof<C>>,
}

/// A batched settlement proof allows including the sender and receiver affirmation proofs
/// with the settlement creation proof to reduce the number of transactions
/// required to finalize a settlement.
#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatchedSettlementProof<
    T: DartLimits = (),
    C: CurveTreeConfig = AssetTreeConfig,
    A: CurveTreeConfig = AccountTreeConfig,
> {
    /// The settlement proof containing the memo, root, and legs.
    pub settlement: SettlementProof<T, C>,

    /// The leg affirmations for each leg in the settlement.
    pub leg_affirmations: BoundedVec<BatchedSettlementLegAffirmations<A>, T::MaxSettlementLegs>,
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
> BatchedSettlementProof<T, C, A>
{
    /// Get leg and sender/receiver affirmation counts.
    pub fn count_leg_affirmations(&self) -> SettlementCounts {
        let mut leg_count = 0;
        let mut sender_count = 0;
        let mut receiver_count = 0;

        for leg_aff in &self.leg_affirmations {
            leg_count += 1;
            if leg_aff.sender.is_some() {
                sender_count += 1;
            }
            if leg_aff.receiver.is_some() {
                receiver_count += 1;
            }
        }

        SettlementCounts {
            leg_count,
            sender_count,
            receiver_count,
            mediator_count: 0,
        }
    }

    /// Check leg references in affirmation proofs.
    ///
    /// Returns `true` if all leg references match the settlement legs.
    pub fn check_leg_references(&self) -> bool {
        let settlement = self.settlement.settlement_ref();
        for (idx, leg_aff) in self.leg_affirmations.iter().enumerate() {
            let leg_ref = LegRef::new(settlement, idx as LegId);
            if let Some(sender) = &leg_aff.sender {
                if sender.leg_ref != leg_ref {
                    return false;
                }
            }
            if let Some(receiver) = &leg_aff.receiver {
                if receiver.leg_ref != leg_ref {
                    return false;
                }
            }
        }
        true
    }
}

type BPAffirmAsSenderTxnProof<C> = bp_account::AffirmAsSenderTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The sender affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPAffirmAsSenderTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderAffirmationProof<C>
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
        let state_change = account_asset.get_sender_affirm_state(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsSenderTxnProof::new(
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

            proof: WrappedCanonical::wrap(&proof)?,
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
        let proof = self.proof.decode()?;
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

impl<C: CurveTreeConfig> AccountStateUpdate for SenderAffirmationProof<C> {
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

type BPAffirmAsReceiverTxnProof<C> = bp_account::AffirmAsReceiverTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The receiver affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct ReceiverAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPAffirmAsReceiverTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> ReceiverAffirmationProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the receiver affirmation.
        let state_change = account_asset.get_receiver_affirm_state(account)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsReceiverTxnProof::new(
            rng,
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

            proof: WrappedCanonical::wrap(&proof)?,
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
        let proof = self.proof.decode()?;
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

impl<C: CurveTreeConfig> AccountStateUpdate for ReceiverAffirmationProof<C> {
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

type BPClaimReceivedTxnProof<C> = bp_account::ClaimReceivedTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The proof for claiming received assets in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct ReceiverClaimProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPClaimReceivedTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> ReceiverClaimProof<C>
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
        // Generate a new account state for claiming received assets.
        let state_change = account_asset.get_state_for_claiming_received(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::ClaimReceivedTxnProof::new(
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

            proof: WrappedCanonical::wrap(&proof)?,
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
                log::error!("Invalid root for receiver claim proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
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

impl<C: CurveTreeConfig> AccountStateUpdate for ReceiverClaimProof<C> {
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

type BPSenderCounterUpdateTxnProof<C> = bp_account::SenderCounterUpdateTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// Sender counter update proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderCounterUpdateProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPSenderCounterUpdateTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderCounterUpdateProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for decreasing the counter.
        let state_change = account_asset.get_state_for_decreasing_counter(account)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderCounterUpdateTxnProof::new(
            rng,
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

            proof: WrappedCanonical::wrap(&proof)?,
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
                log::error!("Invalid root for sender counter update proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
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

impl<C: CurveTreeConfig> AccountStateUpdate for SenderCounterUpdateProof<C> {
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

type BPSenderReverseTxnProof<C> = bp_account::SenderReverseTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// Sender reversal proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderReversalProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPSenderReverseTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderReversalProof<C>
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
        // Generate a new account state for reversing the send.
        let state_change = account_asset.get_state_for_reversing_send(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderReverseTxnProof::new(
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

            proof: WrappedCanonical::wrap(&proof)?,
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
                log::error!("Invalid root for sender reversal proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
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

impl<C: CurveTreeConfig> AccountStateUpdate for SenderReversalProof<C> {
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

/// Mediator affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct MediatorAffirmationProof {
    pub leg_ref: LegRef,
    pub accept: bool,
    pub key_index: MediatorId,

    proof: WrappedCanonical<bp_leg::MediatorTxnProof<PallasA>>,
}

impl MediatorAffirmationProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        asset_id: AssetId,
        leg_enc: &LegEncrypted,
        mediator_sk: &EncryptionKeyPair,
        key_index: MediatorId,
        accept: bool,
    ) -> Result<Self, Error> {
        let ctx = leg_ref.context();
        let proof = bp_leg::MediatorTxnProof::new(
            rng,
            leg_enc.decode()?,
            asset_id,
            mediator_sk.secret.0.0,
            accept,
            key_index as usize,
            ctx.as_bytes(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            accept,
            key_index,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify(&self, leg_enc: &LegEncrypted) -> Result<(), Error> {
        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            leg_enc.decode()?,
            self.accept,
            self.key_index as usize,
            ctx.as_bytes(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}
