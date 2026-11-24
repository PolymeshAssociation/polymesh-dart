use codec::{Decode, DecodeWithMemTracking, Encode};
use scale_info::TypeInfo;

use rand_core::{CryptoRng, RngCore};

use bounded_collections::BoundedVec;

use super::*;
use polymesh_dart_bp::leg::mediator;
use polymesh_dart_common::{LegId, MediatorId};

/// Represents the affirmation proofs for each leg in a settlement.
/// This includes the sender, and receiver affirmation proofs.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatchedSettlementLegAffirmations<
    T: DartLimits = (),
    C: CurveTreeConfig = AccountTreeConfig,
> {
    /// The sender's affirmation proof.
    pub sender: Option<SenderAffirmationProof<T, C>>,
    /// The receiver's affirmation proof.
    pub receiver: Option<ReceiverAffirmationProof<T, C>>,
}

/// A batched settlement proof allows including the sender and receiver affirmation proofs
/// with the settlement creation proof to reduce the number of transactions
/// required to finalize a settlement.
#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatchedSettlementProof<
    T: DartLimits = (),
    C: CurveTreeConfig = AssetTreeConfig,
    A: CurveTreeConfig = AccountTreeConfig,
> {
    /// The settlement proof containing the memo, root, and legs.
    pub settlement: SettlementProof<T, C>,

    /// The leg affirmations for each leg in the settlement.
    pub leg_affirmations: BoundedVec<BatchedSettlementLegAffirmations<T, A>, T::MaxSettlementLegs>,
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

/// The affirmation proof depends on whether the leg's asset-id is hidden or revealed.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub enum MediatorAffirmationInner<T: DartLimits = ()> {
    /// Ring affirmation over the mediator entry of a leg with hidden asset-id.
    Hidden(BoundedCanonical<mediator::MediatorTxnProof<PallasA>, T::MaxInnerProofSize>),
    /// Proof of knowledge of the affirmation key. Used when the asset-id is revealed as the
    /// mediator's affirmation key is then known to the verifier and the leg has no mediator entry.
    Revealed(
        BoundedCanonical<mediator::PublicAssetMediatorTxnProof<PallasA>, T::MaxInnerProofSize>,
    ),
}

/// Mediator affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct MediatorAffirmationProof<T: DartLimits = ()> {
    pub leg_ref: LegRef,
    pub accept: bool,
    /// The mediator's index in the leg encryption when the asset-id is hidden, else its position in
    /// the asset's registered mediators.
    pub key_index: MediatorId,

    inner: MediatorAffirmationInner<T>,
}

impl<T: DartLimits> MediatorAffirmationProof<T> {
    /// Affirm or reject a leg. Uses the ring affirmation when the leg's asset-id is hidden and the
    /// proof of knowledge of the affirmation key when it is revealed.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        leg_enc: &LegEncrypted,
        mediator_keys: &AccountKeys,
        key_index: MediatorId,
        accept: bool,
    ) -> Result<Self, Error> {
        Self::new_with_context(rng, leg_ref, &[], leg_enc, mediator_keys, key_index, accept)
    }

    pub fn new_with_context<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        ctx: &[u8],
        leg_enc: &LegEncrypted,
        mediator_keys: &AccountKeys,
        key_index: MediatorId,
        accept: bool,
    ) -> Result<Self, Error> {
        let ctx = compose_ctx(ctx, &leg_ref.context());
        let leg_enc = leg_enc.decode()?;
        let core = &leg_enc.leg_enc_core_and_eph_keys.core;
        let inner = if core.is_asset_id_revealed() {
            let proof = mediator::PublicAssetMediatorTxnProof::new(
                rng,
                mediator_keys.acct.secret.0.0,
                key_index as usize,
                accept,
                &ctx,
                core,
                &leg_enc.eph_pk_enc_keys,
                &mediator_keys.acct.public.get_affine()?,
                &dart_gens().sig_key_gen(),
            )?;
            MediatorAffirmationInner::Revealed(BoundedCanonical::wrap(&proof)?)
        } else {
            let med = leg_enc.mediator_encryption(key_index as usize)?;
            // The mediator's encryption key is one of the asset's and its index is found by trial
            // decryption. The ring hides it so it must not be stored or sent anywhere.
            let i = med.find_key_index(
                &mediator_keys.enc.secret.0.0,
                &mediator_keys.acct.public.get_affine()?,
            )?;
            let proof = mediator::MediatorTxnProof::new(
                rng,
                mediator_keys.acct.secret.0.0,
                mediator_keys.enc.secret.0.0,
                key_index as usize,
                i,
                accept,
                &ctx,
                core,
                &leg_enc.eph_pk_enc_keys,
                med,
                dart_gens().sig_key_gen(),
            )?;
            MediatorAffirmationInner::Hidden(BoundedCanonical::wrap(&proof)?)
        };

        Ok(Self {
            leg_ref: leg_ref.clone(),
            accept,
            key_index,

            inner,
        })
    }

    /// Is the asset-id of the leg revealed?
    pub fn is_asset_id_revealed(&self) -> bool {
        matches!(self.inner, MediatorAffirmationInner::Revealed(_))
    }

    /// Verify against the leg. `lookup` returns the asset's registered mediator key at the given
    /// position and is called only when the leg's asset-id is revealed.
    pub fn verify(
        &self,
        leg_enc: &LegEncrypted,
        lookup: impl FnOnce(AssetId, MediatorId) -> Result<AccountPublicKey, Error>,
    ) -> Result<(), Error> {
        self.verify_with_context(&[], leg_enc, lookup)
    }

    pub fn verify_with_context(
        &self,
        ctx: &[u8],
        leg_enc: &LegEncrypted,
        lookup: impl FnOnce(AssetId, MediatorId) -> Result<AccountPublicKey, Error>,
    ) -> Result<(), Error> {
        let ctx = compose_ctx(ctx, &self.leg_ref.context());
        let leg_enc = leg_enc.decode()?;
        let core = &leg_enc.leg_enc_core_and_eph_keys.core;
        match (&self.inner, core.asset_id()) {
            (MediatorAffirmationInner::Hidden(inner), None) => {
                inner.decode()?.verify(
                    self.key_index as usize,
                    self.accept,
                    &ctx,
                    core,
                    &leg_enc.eph_pk_enc_keys,
                    leg_enc.mediator_encryption(self.key_index as usize)?,
                    dart_gens().sig_key_gen(),
                )?;
            }
            (MediatorAffirmationInner::Revealed(inner), Some(asset_id)) => {
                let mediator_pk = lookup(asset_id, self.key_index)?;
                inner.decode()?.verify(
                    self.key_index as usize,
                    self.accept,
                    &ctx,
                    core,
                    &leg_enc.eph_pk_enc_keys,
                    &mediator_pk.get_affine()?,
                    &dart_gens().sig_key_gen(),
                    None,
                )?;
            }
            _ => return Err(Error::InvalidProofType),
        }
        Ok(())
    }
}
