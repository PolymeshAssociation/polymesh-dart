use crate::{Error, error};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::format;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use polymesh_dart_common::{AssetId, Balance};

/// Asset-id can be encrypted or revealed by the leg creator
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AssetIdEncryption<G: AffineRepr> {
    /// asset-id as encrypted
    Ciphertext(G),
    /// asset-id as revealed
    Revealed(AssetId),
}

impl<G: AffineRepr> AssetIdEncryption<G> {
    pub fn is_revealed(&self) -> bool {
        matches!(self, Self::Revealed(_))
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id(&self) -> Option<AssetId> {
        match self {
            AssetIdEncryption::Ciphertext(_) => None,
            AssetIdEncryption::Revealed(id) => Some(*id),
        }
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id_ciphertext(&self) -> Option<G> {
        match self {
            AssetIdEncryption::Ciphertext(ct) => Some(*ct),
            AssetIdEncryption::Revealed(_) => None,
        }
    }
}

/// Sender's ephemeral public keys. Index 1 is None when the sender cannot decrypt the receiver's pk.
/// Index 3 is None when asset-id is revealed (not encrypted).
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderEphemeralPublicKey<G: AffineRepr> {
    pub r1: G,
    pub r2: Option<G>,
    pub r3: G,
    pub r4: Option<G>,
    pub r5: G,
}

/// Receiver's ephemeral public keys. Index 0 is None when the receiver cannot decrypt the sender's pk.
/// Index 3 is None when asset-id is revealed (not encrypted).
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiverEphemeralPublicKey<G: AffineRepr> {
    pub r1: Option<G>,
    pub r2: G,
    pub r3: G,
    pub r4: Option<G>,
    pub r6: G,
}

/// The party's ephemeral public key — either sender or receiver.
/// Used in affirmation proofs where the same code handles both roles.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PartyEphemeralPublicKey<G: AffineRepr> {
    Sender(SenderEphemeralPublicKey<G>),
    Receiver(ReceiverEphemeralPublicKey<G>),
}

impl<G: AffineRepr> PartyEphemeralPublicKey<G> {
    pub fn is_sender(&self) -> bool {
        matches!(self, Self::Sender(_))
    }

    /// Ephemeral key for amount encryption (index 2) — always present for both parties
    pub fn eph_pk_amount(&self) -> G {
        match self {
            Self::Sender(s) => s.r3,
            Self::Receiver(r) => r.r3,
        }
    }

    /// Ephemeral key for asset_id encryption (index 3) — `None` when asset ID is revealed
    pub fn eph_pk_asset_id(&self) -> Option<G> {
        match self {
            Self::Sender(s) => s.r4,
            Self::Receiver(r) => r.r4,
        }
    }

    /// Ephemeral key identifying the party (index 0 for sender, index 1 for receiver)
    pub fn eph_pk_participant(&self) -> G {
        match self {
            Self::Sender(s) => s.r1,
            Self::Receiver(r) => r.r2,
        }
    }

    /// Ephemeral key identifying the party under its second randomness (`r5` for sender, `r6` for
    /// receiver), tied to the first by `S[0]' = S[0] * (r5 / r1)` (similar for receiver).
    pub fn eph_pk_participant_prime(&self) -> G {
        match self {
            Self::Sender(s) => s.r5,
            Self::Receiver(r) => r.r6,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionCore<G: AffineRepr> {
    pub ct_s: G,
    pub ct_r: G,
    pub ct_amount: G,
    pub ct_asset_id: AssetIdEncryption<G>,
    /// `enc_key_gen * r5`, with ephemeral share `eph_pk_s.r5 = pk_s * r5`. Binds the sender point to
    /// the registered key.
    pub ct_s_prime: G,
    /// `enc_key_gen * r6`, with ephemeral share `eph_pk_r.r6 = pk_r * r6`. Binds the receiver point to
    /// the registered key.
    pub ct_r_prime: G,
}

impl<G: AffineRepr> LegEncryptionCore<G> {
    /// Returns the ciphertext for the participant, `ct_s` for sender, `ct_r` for receiver
    pub fn ct_participant(&self, is_sender: bool) -> G {
        if is_sender { self.ct_s } else { self.ct_r }
    }

    /// Returns the second participant ciphertext, `ct_s_prime` for sender, `ct_r_prime` for receiver
    pub fn ct_participant_prime(&self, is_sender: bool) -> G {
        if is_sender {
            self.ct_s_prime
        } else {
            self.ct_r_prime
        }
    }

    pub fn is_asset_id_revealed(&self) -> bool {
        matches!(self.ct_asset_id, AssetIdEncryption::Revealed(_))
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id(&self) -> Option<AssetId> {
        self.ct_asset_id.asset_id()
    }

    /// `None` when asset-id is revealed (hidden from the verifier).
    pub fn asset_id_ciphertext(&self) -> Option<G> {
        self.ct_asset_id.asset_id_ciphertext()
    }

    pub fn ct_s(&self) -> G {
        self.ct_s
    }

    pub fn ct_r(&self) -> G {
        self.ct_r
    }

    pub fn ct_amount(&self) -> G {
        self.ct_amount
    }
}

mod serialization {
    use super::*;
    use ark_serialize::{Compress, SerializationError, Valid, Validate};
    use ark_std::io::{Read, Write};

    impl<G: AffineRepr> CanonicalSerialize for AssetIdEncryption<G> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                AssetIdEncryption::Ciphertext(ct) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    ct.serialize_with_mode(&mut writer, compress)
                }
                AssetIdEncryption::Revealed(id) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    id.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                AssetIdEncryption::Ciphertext(ct) => ct.serialized_size(compress),
                AssetIdEncryption::Revealed(id) => id.serialized_size(compress),
            }
        }
    }

    impl<G: AffineRepr> CanonicalDeserialize for AssetIdEncryption<G> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            let discriminant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
            match discriminant {
                0 => Ok(AssetIdEncryption::Ciphertext(G::deserialize_with_mode(
                    &mut reader,
                    compress,
                    validate,
                )?)),
                1 => Ok(AssetIdEncryption::Revealed(AssetId::deserialize_with_mode(
                    &mut reader,
                    compress,
                    validate,
                )?)),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G: AffineRepr> Valid for AssetIdEncryption<G> {
        fn check(&self) -> Result<(), SerializationError> {
            match self {
                AssetIdEncryption::Ciphertext(ct) => ct.check(),
                AssetIdEncryption::Revealed(id) => id.check(),
            }
        }
    }

    impl<G: AffineRepr> CanonicalSerialize for PartyEphemeralPublicKey<G> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                PartyEphemeralPublicKey::Sender(eph_pk) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    eph_pk.serialize_with_mode(&mut writer, compress)
                }
                PartyEphemeralPublicKey::Receiver(eph_pk) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    eph_pk.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                PartyEphemeralPublicKey::Sender(eph_pk) => eph_pk.serialized_size(compress),
                PartyEphemeralPublicKey::Receiver(eph_pk) => eph_pk.serialized_size(compress),
            }
        }
    }

    impl<G: AffineRepr> CanonicalDeserialize for PartyEphemeralPublicKey<G> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            let discriminant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
            match discriminant {
                0 => Ok(PartyEphemeralPublicKey::Sender(
                    SenderEphemeralPublicKey::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                1 => Ok(PartyEphemeralPublicKey::Receiver(
                    ReceiverEphemeralPublicKey::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G: AffineRepr> Valid for PartyEphemeralPublicKey<G> {
        fn check(&self) -> Result<(), SerializationError> {
            match self {
                PartyEphemeralPublicKey::Sender(eph_pk) => eph_pk.check(),
                PartyEphemeralPublicKey::Receiver(eph_pk) => eph_pk.check(),
            }
        }
    }
}

/// Configuration for a leg in common state change operations (prover side)
#[derive(Clone)]
pub struct LegProverConfig<G: AffineRepr> {
    pub encryption: LegEncryptionCore<G>,
    pub party_eph_pk: PartyEphemeralPublicKey<G>,
    /// Checked against `ct_amount` by the auth proof prover.
    pub amount: Balance,
    /// Asset-id of the leg. Checked against `ct_asset_id`, or the revealed asset-id, by the auth
    /// proof prover.
    pub asset_id: AssetId,
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

/// Errors unless the amount response is present if `needs_amount` and the asset-id response is
/// present if the asset-id is encrypted in the leg.
pub fn ensure_expected_leg_link_responses(
    leg_index: usize,
    has_resp_amount: bool,
    has_resp_asset_id: bool,
    needs_amount: bool,
    is_asset_id_revealed: bool,
) -> error::Result<()> {
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

/// The single revealed asset id (`None` if all legs hide it) and the count of hidden-asset-id legs,
/// erroring when `check_same_asset` and two revealed legs disagree.
fn asset_id_and_hidden_count_inner(
    legs: impl Iterator<Item = (bool, Option<AssetId>)>,
    check_same_asset: bool,
) -> error::Result<(Option<AssetId>, usize)> {
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
    pub fn asset_id_and_hidden_count(configs: &[Self]) -> error::Result<(Option<AssetId>, usize)> {
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
    pub fn asset_id_and_hidden_count(configs: &[Self]) -> error::Result<(Option<AssetId>, usize)> {
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
    pub fn check_balance_order(configs: &[Self]) -> error::Result<()> {
        let directions: Vec<Option<bool>> =
            configs.iter().map(|c| c.has_balance_decreased).collect();
        check_balance_directions(&directions)
    }
}

/// Checks if follows canonical per-account leg order where balance increases before decreases so it
/// never goes negative. This is just to make it easy for off-chain processors.
pub fn check_balance_directions(directions: &[Option<bool>]) -> error::Result<()> {
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
