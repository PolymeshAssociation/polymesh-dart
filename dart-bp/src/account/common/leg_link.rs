use crate::account::{AccountState, AccountStateCommitment, PartyEphemeralPublicKey};
use crate::leg::LegEncryptionCore;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use polymesh_dart_common::Balance;
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment,
};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Per-leg link binding the affirming account to the leg via one `enc_gen`-generator ciphertext
/// relation. `ct_amount` when the asset-id is revealed in this leg, else `ct_asset_id`.
/// `sk_enc^-1` is shared from the randomness BP. For `ct_amount`, `v` is owned here and shared into
/// the balance BP, for hidden `asset_id` is shared from the  account commitment.

#[derive(Clone, Debug)]
pub enum RespAssetId<G0: SWCurveConfig> {
    /// `ct_asset_id = Eph_at * sk_enc^-1 + enc_gen * asset_id`, `sk_enc^-1` and `asset_id` shared
    Hidden(PartialPokPedersenCommitment<Affine<G0>>),
    /// `ct_asset_id - enc_gen * at = Eph_at * sk_enc^-1`, `sk_enc^-1` shared
    Elsewhere(PartialPokDiscreteLog<Affine<G0>>),
}

#[derive(Clone, Debug)]
pub enum LegAccountLink<G0: SWCurveConfig> {
    /// asset-id revealed in this leg: `ct_amount = Eph_amt * sk_enc^-1 + enc_gen * v`
    AmountOnly {
        resp_amount: Partial2PokPedersenCommitment<Affine<G0>>,
    },
    /// asset-id encrypted, balance unchanged
    AssetIdOnly { resp_asset_id: RespAssetId<G0> },
    /// asset-id encrypted, balance changed
    AssetIdAndAmount {
        resp_asset_id: RespAssetId<G0>,
        resp_amount: Partial2PokPedersenCommitment<Affine<G0>>,
    },
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub enum AssetIdProtocol<G0: SWCurveConfig> {
    Hidden(PokPedersenCommitmentProtocol<Affine<G0>>),
    Elsewhere(PokDiscreteLogProtocol<Affine<G0>>),
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub enum LegAccountLinkProtocol<G0: SWCurveConfig> {
    AmountOnly {
        t_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
    },
    AssetIdOnly {
        t_asset_id: AssetIdProtocol<G0>,
    },
    AssetIdAndAmount {
        t_asset_id: AssetIdProtocol<G0>,
        t_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
    },
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
    pub fn t_amount(&self) -> Option<&PokPedersenCommitmentProtocol<Affine<G0>>> {
        match self {
            Self::AmountOnly { t_amount } => Some(t_amount),
            Self::AssetIdAndAmount { t_amount, .. } => Some(t_amount),
            Self::AssetIdOnly { .. } => None,
        }
    }

    pub fn t_asset_id(&self) -> Option<&AssetIdProtocol<G0>> {
        match self {
            Self::AssetIdOnly { t_asset_id } => Some(t_asset_id),
            Self::AssetIdAndAmount { t_asset_id, .. } => Some(t_asset_id),
            Self::AmountOnly { .. } => None,
        }
    }

    pub fn gen_proof(&self, challenge: &G0::ScalarField) -> LegAccountLink<G0> {
        match self {
            Self::AmountOnly { t_amount } => LegAccountLink::AmountOnly {
                resp_amount: t_amount.clone().gen_partial2_proof(challenge),
            },
            Self::AssetIdOnly { t_asset_id } => LegAccountLink::AssetIdOnly {
                resp_asset_id: t_asset_id.gen_proof(),
            },
            Self::AssetIdAndAmount {
                t_asset_id,
                t_amount,
            } => LegAccountLink::AssetIdAndAmount {
                resp_asset_id: t_asset_id.gen_proof(),
                resp_amount: t_amount.clone().gen_partial2_proof(challenge),
            },
        }
    }
}

impl<G0: SWCurveConfig> LegAccountLink<G0> {
    pub fn resp_amount(&self) -> Option<&Partial2PokPedersenCommitment<Affine<G0>>> {
        match self {
            Self::AmountOnly { resp_amount } => Some(resp_amount),
            Self::AssetIdAndAmount { resp_amount, .. } => Some(resp_amount),
            Self::AssetIdOnly { .. } => None,
        }
    }

    pub fn resp_asset_id(&self) -> Option<&RespAssetId<G0>> {
        match self {
            Self::AssetIdOnly { resp_asset_id } => Some(resp_asset_id),
            Self::AssetIdAndAmount { resp_asset_id, .. } => Some(resp_asset_id),
            Self::AmountOnly { .. } => None,
        }
    }
}

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

impl<G: AffineRepr> LegProverConfig<G> {
    pub fn is_asset_id_revealed(&self) -> bool {
        self.encryption.is_asset_id_revealed()
    }

    /// `ct_amount` is proven when the leg reveals its asset-id or the balance changes
    pub fn needs_ct_amount(&self) -> bool {
        self.is_asset_id_revealed() || self.has_balance_changed
    }

    pub fn is_asset_id_revealed_in_any(configs: &[Self]) -> bool {
        configs
            .iter()
            .any(|config| config.encryption.is_asset_id_revealed())
    }

    pub fn has_balance_changed(configs: &[Self]) -> bool {
        configs.iter().any(|config| config.has_balance_changed)
    }

    pub fn num_hidden_asset_ids(configs: &[Self]) -> usize {
        configs
            .iter()
            .filter(|l| !l.encryption.is_asset_id_revealed())
            .count()
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

    pub fn is_asset_id_revealed_in_any(configs: &[Self]) -> bool {
        configs
            .iter()
            .any(|config| config.encryption.is_asset_id_revealed())
    }

    pub fn has_balance_changed(configs: &[Self]) -> bool {
        configs
            .iter()
            .any(|config| config.has_balance_decreased.is_some())
    }

    pub fn num_hidden_asset_ids(configs: &[Self]) -> usize {
        configs
            .iter()
            .filter(|l| !l.encryption.is_asset_id_revealed())
            .count()
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

    impl<G0: SWCurveConfig> CanonicalSerialize for LegAccountLink<G0> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                LegAccountLink::AmountOnly { resp_amount } => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    resp_amount.serialize_with_mode(&mut writer, compress)
                }
                LegAccountLink::AssetIdOnly { resp_asset_id } => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    resp_asset_id.serialize_with_mode(&mut writer, compress)
                }
                LegAccountLink::AssetIdAndAmount {
                    resp_asset_id,
                    resp_amount,
                } => {
                    2u8.serialize_with_mode(&mut writer, compress)?;
                    resp_asset_id.serialize_with_mode(&mut writer, compress)?;
                    resp_amount.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                LegAccountLink::AmountOnly { resp_amount } => resp_amount.serialized_size(compress),
                LegAccountLink::AssetIdOnly { resp_asset_id } => {
                    resp_asset_id.serialized_size(compress)
                }
                LegAccountLink::AssetIdAndAmount {
                    resp_asset_id,
                    resp_amount,
                } => {
                    resp_asset_id.serialized_size(compress) + resp_amount.serialized_size(compress)
                }
            }
        }
    }

    impl<G0: SWCurveConfig> CanonicalDeserialize for LegAccountLink<G0> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            match u8::deserialize_with_mode(&mut reader, compress, validate)? {
                0 => Ok(LegAccountLink::AmountOnly {
                    resp_amount: Partial2PokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                1 => Ok(LegAccountLink::AssetIdOnly {
                    resp_asset_id: RespAssetId::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                2 => Ok(LegAccountLink::AssetIdAndAmount {
                    resp_asset_id: RespAssetId::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                    resp_amount: Partial2PokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G0: SWCurveConfig> Valid for LegAccountLink<G0> {
        fn check(&self) -> Result<(), SerializationError> {
            match self {
                LegAccountLink::AmountOnly { resp_amount } => resp_amount.check(),
                LegAccountLink::AssetIdOnly { resp_asset_id } => resp_asset_id.check(),
                LegAccountLink::AssetIdAndAmount {
                    resp_asset_id,
                    resp_amount,
                } => {
                    resp_asset_id.check()?;
                    resp_amount.check()
                }
            }
        }
    }
}
