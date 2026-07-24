use crate::Error;
use crate::error::Result;
use crate::leg::{LegEncryptionCore, PartyEphemeralPublicKey};
use ark_ec::AffineRepr;
use ark_std::string::ToString;
use polymesh_dart_common::{AssetId, Balance};

/// Configuration for a leg in common state change operations (prover side)
#[derive(Clone)]
pub struct LegProverConfig<G: AffineRepr> {
    pub encryption: LegEncryptionCore<G>,
    pub party_eph_pk: PartyEphemeralPublicKey<G>,
    pub amount: Balance,
    pub has_balance_changed: bool,
}

/// Configuration for a leg in common state change operations (verifier side)
#[derive(Clone)]
pub struct LegVerifierConfig<G: AffineRepr> {
    pub encryption: LegEncryptionCore<G>,
    pub party_eph_pk: PartyEphemeralPublicKey<G>,
    pub has_balance_decreased: Option<bool>,
    pub has_counter_decreased: Option<bool>,
}

/// The single revealed asset id (`None` if all legs hide it) and the count of hidden-asset-id legs,
/// erroring when `check_same_asset` and two revealed legs disagree.
fn asset_id_and_hidden_count_inner(
    legs: impl Iterator<Item = (bool, Option<AssetId>)>,
    check_same_asset: bool,
) -> Result<(Option<AssetId>, usize)> {
    let mut asset_id = None;
    let mut num_hidden = 0;
    for (is_revealed, leg_asset_id) in legs {
        if is_revealed {
            match asset_id {
                None => asset_id = leg_asset_id,
                Some(a) if check_same_asset && leg_asset_id != Some(a) => {
                    return Err(Error::ProofVerificationError(
                        "All legs must have the same asset id".to_string(),
                    ));
                }
                _ => {}
            }
        } else {
            num_hidden += 1;
        }
    }
    Ok((asset_id, num_hidden))
}

impl<G: AffineRepr> LegProverConfig<G> {
    pub fn is_asset_id_revealed(&self) -> bool {
        self.encryption.is_asset_id_revealed()
    }

    /// `ct_amount` is proven when the leg reveals its asset-id or the balance changes
    pub fn needs_ct_amount(&self) -> bool {
        self.is_asset_id_revealed() || self.has_balance_changed
    }

    /// Prover skips the same-asset check under ignore_prover_input_sanitation; verifier always checks.
    pub fn asset_id_and_hidden_count(configs: &[Self]) -> Result<(Option<AssetId>, usize)> {
        asset_id_and_hidden_count_inner(
            configs
                .iter()
                .map(|c| (c.is_asset_id_revealed(), c.encryption.asset_id())),
            !cfg!(feature = "ignore_prover_input_sanitation"),
        )
    }

    pub fn has_balance_changed(configs: &[Self]) -> bool {
        configs.iter().any(|config| config.has_balance_changed)
    }

    pub fn num_ct_amounts(configs: &[Self]) -> usize {
        configs.iter().filter(|l| l.needs_ct_amount()).count()
    }
}

impl<G: AffineRepr> LegVerifierConfig<G> {
    pub fn is_asset_id_revealed(&self) -> bool {
        self.encryption.is_asset_id_revealed()
    }

    pub fn needs_ct_amount(&self) -> bool {
        self.is_asset_id_revealed() || self.has_balance_decreased.is_some()
    }

    pub fn has_balance_changed(configs: &[Self]) -> bool {
        configs
            .iter()
            .any(|config| config.has_balance_decreased.is_some())
    }

    /// The single revealed asset id (`None` if all legs hide it) and the count of hidden-asset-id legs,
    /// erroring if two revealed legs disagree.
    pub fn asset_id_and_hidden_count(configs: &[Self]) -> Result<(Option<AssetId>, usize)> {
        asset_id_and_hidden_count_inner(
            configs
                .iter()
                .map(|c| (c.is_asset_id_revealed(), c.encryption.asset_id())),
            true,
        )
    }

    pub fn num_balance_changes(configs: &[Self]) -> usize {
        configs
            .iter()
            .filter(|l| l.has_balance_decreased.is_some())
            .count()
    }

    pub fn num_ct_amounts(configs: &[Self]) -> usize {
        configs.iter().filter(|l| l.needs_ct_amount()).count()
    }
}
