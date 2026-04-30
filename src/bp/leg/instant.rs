use codec::{Decode, DecodeWithMemTracking, Encode};
use scale_info::TypeInfo;

use ark_ec::CurveConfig;
use bounded_collections::BoundedVec;

use crate::curve_tree::*;
use crate::*;
use polymesh_dart_common::LegId;

/// Represents the affirmation proofs for each leg in a settlement.
/// This includes the sender, and receiver affirmation proofs.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct InstantSettlementLegAffirmations<
    T: DartLimits = (),
    C: CurveTreeConfig = AccountTreeConfig,
> {
    /// The sender's affirmation proof.
    pub sender: InstantSenderAffirmationProof<T, C>,
    /// The receiver's affirmation proof.
    pub receiver: InstantReceiverAffirmationProof<T, C>,
    /// The mediator affirmation proofs.
    pub mediators: BoundedVec<MediatorAffirmationProof, T::MaxAssetMediators>,
}

/// A batched settlement proof allows including the sender and receiver affirmation proofs
/// with the settlement creation proof to reduce the number of transactions
/// required to finalize a settlement.
#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, TypeInfo, PartialEq, Eq)]
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
    /// Leg count.
    pub fn leg_count(&self) -> usize {
        self.settlement.legs.len()
    }

    /// Settlement reference.
    pub fn settlement_ref(&self) -> SettlementRef {
        self.settlement.settlement_ref()
    }

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
