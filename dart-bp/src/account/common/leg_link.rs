use crate::Error;
use crate::account::{AccountState, AccountStateCommitment, PartyEphemeralPublicKey};
use crate::error::Result;
use crate::leg::LegEncryptionCore;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::format;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use polymesh_dart_common::{AssetId, Balance};
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment,
};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Per-leg link binding the affirming account to the leg. The participant relations
/// `ct_participant = eph_pk_participant * sk_enc^-1 + enc_key_gen * sk_enc` and
/// `ct_participant_prime = eph_pk_participant_prime * sk_enc^-1` are always proved and bind the leg party point
/// to the account's encryption key. `ct_amount` is proved when the balance changes, and `ct_asset_id`
/// when the asset-id is hidden.
/// `sk_enc^-1` is shared from the randomness BP and `sk_enc` from the account commitment. For
/// `ct_amount`, `v` is owned here and shared into the balance BP. For hidden `asset_id`, `asset_id`
/// is shared from the account commitment.
#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct LegAccountLinkProtocol<G0: SWCurveConfig> {
    pub t_participant: PokPedersenCommitmentProtocol<Affine<G0>>,
    pub t_participant_prime: PokDiscreteLogProtocol<Affine<G0>>,
    /// Present when the balance changes.
    pub t_amount: Option<PokPedersenCommitmentProtocol<Affine<G0>>>,
    /// Present when the asset-id is encrypted in this leg.
    pub t_asset_id: Option<AssetIdProtocol<G0>>,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegAccountLink<G0: SWCurveConfig> {
    pub resp_participant: PartialPokPedersenCommitment<Affine<G0>>,
    pub resp_participant_prime: PartialPokDiscreteLog<Affine<G0>>,
    /// `ct_amount = Eph_amt * sk_enc^-1 + enc_gen * v`. Present when the balance changes.
    pub resp_amount: Option<Partial2PokPedersenCommitment<Affine<G0>>>,
    /// Present when the asset-id is encrypted in this leg.
    pub resp_asset_id: Option<RespAssetId<G0>>,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub enum AssetIdProtocol<G0: SWCurveConfig> {
    /// Asset id is hidden in all legs considered in the proof
    Hidden(PokPedersenCommitmentProtocol<Affine<G0>>),
    /// Asset id is hidden in this leg but revealed elsewhere in the proof
    Elsewhere(PokDiscreteLogProtocol<Affine<G0>>),
}

#[derive(Clone, Debug)]
pub enum RespAssetId<G0: SWCurveConfig> {
    /// `ct_asset_id = Eph_at * sk_enc^-1 + enc_gen * asset_id`, `sk_enc^-1` and `asset_id` shared
    Hidden(PartialPokPedersenCommitment<Affine<G0>>),
    /// `ct_asset_id - enc_gen * at = Eph_at * sk_enc^-1`, `sk_enc^-1` shared
    Elsewhere(PartialPokDiscreteLog<Affine<G0>>),
}

impl<G0: SWCurveConfig> AssetIdProtocol<G0> {
    pub fn gen_proof(&self) -> RespAssetId<G0> {
        match self {
            Self::Hidden(p) => RespAssetId::Hidden(p.clone().gen_partial_proof()),
            Self::Elsewhere(p) => RespAssetId::Elsewhere(p.clone().gen_partial_proof()),
        }
    }
}

impl<G0: SWCurveConfig> LegAccountLinkProtocol<G0> {
    pub fn gen_proof(&self, challenge: &G0::ScalarField) -> LegAccountLink<G0> {
        LegAccountLink {
            resp_participant: self.t_participant.clone().gen_partial_proof(),
            resp_participant_prime: self.t_participant_prime.clone().gen_partial_proof(),
            resp_amount: self
                .t_amount
                .as_ref()
                .map(|t| t.clone().gen_partial2_proof(challenge)),
            resp_asset_id: self.t_asset_id.as_ref().map(|t| t.gen_proof()),
        }
    }
}

impl<G0: SWCurveConfig> LegAccountLink<G0> {
    /// Errors unless `resp_amount` is present if `needs_amount` and `resp_asset_id` is present if
    /// the asset-id is encrypted in the leg.
    pub fn ensure_expected_responses(
        &self,
        leg_index: usize,
        needs_amount: bool,
        is_asset_id_revealed: bool,
    ) -> Result<()> {
        ensure_expected_leg_link_responses(
            leg_index,
            self.resp_amount.is_some(),
            self.resp_asset_id.is_some(),
            needs_amount,
            is_asset_id_revealed,
        )
    }
}

/// Errors unless the amount response is present if `needs_amount` and the asset-id response is
/// present if the asset-id is encrypted in the leg.
pub fn ensure_expected_leg_link_responses(
    leg_index: usize,
    has_resp_amount: bool,
    has_resp_asset_id: bool,
    needs_amount: bool,
    is_asset_id_revealed: bool,
) -> Result<()> {
    if has_resp_amount != needs_amount {
        return Err(Error::ProofVerificationError(format!(
            "Leg {leg_index}: amount response present = {has_resp_amount}, expected {needs_amount}"
        )));
    }
    if has_resp_asset_id == is_asset_id_revealed {
        return Err(Error::ProofVerificationError(format!(
            "Leg {leg_index}: asset-id response present = {has_resp_asset_id}, expected {}",
            !is_asset_id_revealed
        )));
    }
    Ok(())
}

/// Per-leg action tag to be added to proof transcript. The tag binds whether the balance and the
/// counter changes.
pub fn leg_action_tag(has_balance_changed: bool, has_counter_decreased: Option<bool>) -> [u8; 2] {
    let counter = match has_counter_decreased {
        None => 0,
        Some(false) => 1,
        Some(true) => 2,
    };
    [has_balance_changed as u8, counter]
}

/// Configuration for a leg in common state change operations (prover side)
#[derive(Clone)]
pub struct LegProverConfig<G: AffineRepr> {
    pub encryption: LegEncryptionCore<G>,
    pub party_eph_pk: PartyEphemeralPublicKey<G>,
    pub amount: Balance,
    pub has_balance_changed: bool,
    /// `None` when the counter doesn't change on this leg.
    pub has_counter_decreased: Option<bool>,
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

    /// `ct_amount` is proven only when this leg changes the account's balance.
    pub fn needs_ct_amount(&self) -> bool {
        self.has_balance_changed
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

    pub fn action_tag(&self) -> [u8; 2] {
        leg_action_tag(self.has_balance_changed, self.has_counter_decreased)
    }
}

impl<G: AffineRepr> LegVerifierConfig<G> {
    pub fn is_asset_id_revealed(&self) -> bool {
        self.encryption.is_asset_id_revealed()
    }

    pub fn needs_ct_amount(&self) -> bool {
        self.has_balance_decreased.is_some()
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

    pub fn action_tag(&self) -> [u8; 2] {
        leg_action_tag(
            self.has_balance_decreased.is_some(),
            self.has_counter_decreased,
        )
    }

    /// Increases-first check on verifier leg configs.
    pub fn check_balance_order(configs: &[Self]) -> Result<()> {
        let directions: Vec<Option<bool>> =
            configs.iter().map(|c| c.has_balance_decreased).collect();
        check_balance_directions(&directions)
    }
}

/// Checks if follows canonical per-account leg order where balance increases before decreases so it
/// never goes negative. This is just to make it easy for off-chain processors.
pub fn check_balance_directions(directions: &[Option<bool>]) -> Result<()> {
    let mut seen_decrease = false;
    for dir in directions {
        match dir {
            None => {}
            Some(true) => seen_decrease = true,
            Some(false) => {
                if seen_decrease {
                    return Err(Error::ProofVerificationError(
                        "Balance increases must come before decreases".to_string(),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Permutation sorting leg indices increases-first, stable within each group.
/// `directions[i]` is the balance direction of leg `i`: `Some(false)` increase,
/// `Some(true)` decrease, `None` no change. Callers apply the result to every
/// per-leg array (leg refs, `k_amounts`, configs) before proving.
pub fn balance_order_permutation(directions: &[Option<bool>]) -> Vec<usize> {
    let mut increases = Vec::with_capacity(directions.len());
    let mut rest = Vec::with_capacity(directions.len());
    for (i, d) in directions.iter().enumerate() {
        if *d == Some(false) {
            increases.push(i);
        } else {
            rest.push(i);
        }
    }
    increases.extend(rest);
    increases
}

/// Per-account witness for a solo state-transition prover, secret keys + old and new account states.
#[derive(Clone, Zeroize)]
pub struct AccountTxnWitness<G: AffineRepr> {
    pub sk_aff: G::ScalarField,
    pub sk_enc: G::ScalarField,
    /// Old account state that's being updated
    pub account: AccountState<G>,
    /// New account state after being updated
    pub updated_account: AccountState<G>,
    /// This is public, not a witness but allows one less argument to pass around
    #[zeroize(skip)]
    pub updated_account_commitment: AccountStateCommitment<G>,
}

impl<G: AffineRepr> AccountTxnWitness<G> {
    pub fn new(
        sk_aff: G::ScalarField,
        sk_enc: G::ScalarField,
        account: AccountState<G>,
        updated_account: AccountState<G>,
        updated_account_commitment: AccountStateCommitment<G>,
    ) -> Self {
        Self {
            sk_aff,
            sk_enc,
            account,
            updated_account,
            updated_account_commitment,
        }
    }
}

mod serialization {
    use crate::account::common::leg_link::RespAssetId;
    use crate::account::common::*;

    impl<G0: SWCurveConfig> CanonicalSerialize for RespAssetId<G0> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                RespAssetId::Hidden(p) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    p.serialize_with_mode(&mut writer, compress)
                }
                RespAssetId::Elsewhere(p) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    p.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                RespAssetId::Hidden(p) => p.serialized_size(compress),
                RespAssetId::Elsewhere(p) => p.serialized_size(compress),
            }
        }
    }

    impl<G0: SWCurveConfig> CanonicalDeserialize for RespAssetId<G0> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            match u8::deserialize_with_mode(&mut reader, compress, validate)? {
                0 => Ok(RespAssetId::Hidden(
                    PartialPokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                1 => Ok(RespAssetId::Elsewhere(
                    PartialPokDiscreteLog::deserialize_with_mode(&mut reader, compress, validate)?,
                )),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G0: SWCurveConfig> Valid for RespAssetId<G0> {
        fn check(&self) -> Result<(), SerializationError> {
            match self {
                RespAssetId::Hidden(p) => p.check(),
                RespAssetId::Elsewhere(p) => p.check(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn balance_order_accepts_increases_first() {
        assert!(check_balance_directions(&[]).is_ok());
        assert!(check_balance_directions(&[Some(false), Some(false)]).is_ok());
        assert!(check_balance_directions(&[Some(true), Some(true)]).is_ok());
        assert!(check_balance_directions(&[Some(false), Some(true)]).is_ok());
        assert!(check_balance_directions(&[None, Some(false), None, Some(true), None]).is_ok());
    }

    #[test]
    fn balance_order_rejects_increase_after_decrease() {
        assert!(check_balance_directions(&[Some(true), Some(false)]).is_err());
        assert!(check_balance_directions(&[Some(false), Some(true), Some(false)]).is_err());
    }

    #[test]
    fn balance_order_permutation_is_stable_increases_first() {
        let dirs = [Some(true), None, Some(false), Some(true), Some(false)];
        assert_eq!(balance_order_permutation(&dirs), vec![2, 4, 0, 1, 3]);
        let dirs = [None, Some(true)];
        assert_eq!(balance_order_permutation(&dirs), vec![0, 1]);
    }
}
