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

/// Mediator affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct MediatorAffirmationProof<T: DartLimits = ()> {
    pub leg_ref: LegRef,
    pub accept: bool,
    pub key_index: MediatorId,

    inner: BoundedCanonical<mediator::MediatorTxnProof<PallasA>, T::MaxInnerProofSize>,
}

impl<T: DartLimits> MediatorAffirmationProof<T> {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        leg_enc: &MediatorEncryption,
        mediator_keys: &AccountKeys,
        key_index: MediatorId,
        accept: bool,
    ) -> Result<Self, Error> {
        let ctx = leg_ref.context();
        let proof = mediator::MediatorTxnProof::new(
            rng,
            leg_enc.decode()?,
            mediator_keys.enc.secret.0.0,
            mediator_keys.acct.secret.0.0,
            accept,
            ctx.as_bytes(),
            &dart_gens().sig_key_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            accept,
            key_index,

            inner: BoundedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify(&self, leg_enc: &MediatorEncryption) -> Result<(), Error> {
        let ctx = self.leg_ref.context();
        let proof = self.inner.decode()?;
        proof.verify(
            leg_enc.decode()?,
            self.accept,
            ctx.as_bytes(),
            dart_gens().sig_key_gen(),
            None,
        )?;
        Ok(())
    }
}
