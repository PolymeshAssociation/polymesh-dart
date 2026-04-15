use crate::account::PartyEphemeralPublicKey;
use crate::leg::LegEncryptionCore;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{PartialPokDiscreteLog, PartialPokPedersenCommitment};

/// For proving the leg-account linking relation:
/// There are 3 cases depending on whether the asset-id is revealed in this leg or elsewhere:
///
/// All cases always prove the participant ciphertext relation:
/// `ct_s = eph_pk[0] * {sk_enc^{-1}} + enc_key_gen * sk_enc` (sender)
/// or `ct_r = eph_pk[1] * {sk_enc^{-1}} + enc_key_gen * sk_enc` (receiver)
/// Both witnesses (`sk_enc^{-1}` and `sk_enc`) are shared with other sigma protocols.
///
/// AssetIdHidden - additionally proves `ct_asset_id = eph_pk[3] * {sk_enc^{-1}} + enc_gen * at`
/// Both responses (`sk_enc^{-1}` and `asset_id`) are shared with other sigma protocols.
///
/// AssetIdRevealed - asset-id is revealed in this leg, no additional ciphertext proof needed.
///
/// AssetIdRevealedElsewhere - additionally proves `ct_asset_id - enc_gen * at = eph_pk[3] * {sk_enc^{-1}}`,
/// only witness is `sk_enc^{-1}`. This is the case where the leg itself doesn't reveal asset-id but some
/// other leg reveals it thus the prover reveals asset-id here as well.
#[derive(Clone, Debug)]
pub enum LegAccountLink<G0: SWCurveConfig> {
    /// Participant ciphertext proof + asset-id ciphertext proof
    AssetIdHidden {
        resp_participant: PartialPokPedersenCommitment<Affine<G0>>,
        resp_asset_id: PartialPokPedersenCommitment<Affine<G0>>,
    },
    /// Only participant ciphertext proof (asset-id is revealed, no need to prove knowledge)
    AssetIdRevealed {
        resp_participant: PartialPokPedersenCommitment<Affine<G0>>,
    },
    /// Participant ciphertext proof + discrete-log proof for the asset-id ciphertext
    AssetIdRevealedElsewhere {
        resp_participant: PartialPokPedersenCommitment<Affine<G0>>,
        resp_asset_id: PartialPokDiscreteLog<Affine<G0>>,
    },
}

// TODO: Add zeroize
#[derive(Clone, Debug)]
pub enum LegAccountLinkProtocol<G0: SWCurveConfig> {
    AssetIdHidden {
        t_participant: PokPedersenCommitmentProtocol<Affine<G0>>,
        t_asset_id: PokPedersenCommitmentProtocol<Affine<G0>>,
    },
    AssetIdRevealed {
        t_participant: PokPedersenCommitmentProtocol<Affine<G0>>,
    },
    AssetIdRevealedElsewhere {
        t_participant: PokPedersenCommitmentProtocol<Affine<G0>>,
        t_asset_id: PokDiscreteLogProtocol<Affine<G0>>,
    },
}

impl<G0: SWCurveConfig> LegAccountLinkProtocol<G0> {
    pub fn t_participant(&self) -> &PokPedersenCommitmentProtocol<Affine<G0>> {
        match self {
            Self::AssetIdHidden { t_participant, .. } => t_participant,
            Self::AssetIdRevealed { t_participant } => t_participant,
            Self::AssetIdRevealedElsewhere { t_participant, .. } => t_participant,
        }
    }

    pub fn t_asset_id_pc(&self) -> Option<&PokPedersenCommitmentProtocol<Affine<G0>>> {
        match self {
            Self::AssetIdHidden { t_asset_id, .. } => Some(t_asset_id),
            _ => None,
        }
    }

    pub fn t_asset_id_dl(&self) -> Option<&PokDiscreteLogProtocol<Affine<G0>>> {
        match self {
            Self::AssetIdRevealedElsewhere { t_asset_id, .. } => Some(t_asset_id),
            _ => None,
        }
    }

    pub fn gen_proof(self) -> LegAccountLink<G0> {
        match self {
            Self::AssetIdHidden {
                t_participant,
                t_asset_id,
            } => LegAccountLink::AssetIdHidden {
                resp_participant: t_participant.gen_partial_proof(),
                resp_asset_id: t_asset_id.gen_partial_proof(),
            },
            Self::AssetIdRevealed { t_participant } => LegAccountLink::AssetIdRevealed {
                resp_participant: t_participant.gen_partial_proof(),
            },
            Self::AssetIdRevealedElsewhere {
                t_participant,
                t_asset_id,
            } => LegAccountLink::AssetIdRevealedElsewhere {
                resp_participant: t_participant.gen_partial_proof(),
                resp_asset_id: t_asset_id.gen_partial_proof(),
            },
        }
    }
}

impl<G0: SWCurveConfig> LegAccountLink<G0> {
    pub fn resp_participant(&self) -> &PartialPokPedersenCommitment<Affine<G0>> {
        match self {
            Self::AssetIdHidden {
                resp_participant, ..
            } => resp_participant,
            Self::AssetIdRevealed { resp_participant } => resp_participant,
            Self::AssetIdRevealedElsewhere {
                resp_participant, ..
            } => resp_participant,
        }
    }

    pub fn resp_asset_id_pc(&self) -> Option<&PartialPokPedersenCommitment<Affine<G0>>> {
        match self {
            Self::AssetIdHidden { resp_asset_id, .. } => Some(resp_asset_id),
            _ => None,
        }
    }

    pub fn resp_asset_id_dl(&self) -> Option<&PartialPokDiscreteLog<Affine<G0>>> {
        match self {
            Self::AssetIdRevealedElsewhere { resp_asset_id, .. } => Some(resp_asset_id),
            _ => None,
        }
    }
}

/// Configuration for a leg in common state change operations (prover side)
#[derive(Clone)]
pub struct LegProverConfig<G: AffineRepr> {
    pub encryption: LegEncryptionCore<G>,
    pub party_eph_pk: PartyEphemeralPublicKey<G>,
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
}

impl<G: AffineRepr> LegVerifierConfig<G> {
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
}

mod serialization {
    use crate::account::common::*;

    impl<G0: SWCurveConfig> CanonicalSerialize for LegAccountLink<G0> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                LegAccountLink::AssetIdHidden {
                    resp_participant,
                    resp_asset_id,
                } => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    resp_participant.serialize_with_mode(&mut writer, compress)?;
                    resp_asset_id.serialize_with_mode(&mut writer, compress)
                }
                LegAccountLink::AssetIdRevealed { resp_participant } => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    resp_participant.serialize_with_mode(&mut writer, compress)
                }
                LegAccountLink::AssetIdRevealedElsewhere {
                    resp_participant,
                    resp_asset_id,
                } => {
                    2u8.serialize_with_mode(&mut writer, compress)?;
                    resp_participant.serialize_with_mode(&mut writer, compress)?;
                    resp_asset_id.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                LegAccountLink::AssetIdHidden {
                    resp_participant,
                    resp_asset_id,
                } => {
                    resp_participant.serialized_size(compress)
                        + resp_asset_id.serialized_size(compress)
                }
                LegAccountLink::AssetIdRevealed { resp_participant } => {
                    resp_participant.serialized_size(compress)
                }
                LegAccountLink::AssetIdRevealedElsewhere {
                    resp_participant,
                    resp_asset_id,
                } => {
                    resp_participant.serialized_size(compress)
                        + resp_asset_id.serialized_size(compress)
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
                0 => Ok(LegAccountLink::AssetIdHidden {
                    resp_participant: PartialPokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                    resp_asset_id: PartialPokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                1 => Ok(LegAccountLink::AssetIdRevealed {
                    resp_participant: PartialPokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                }),
                2 => Ok(LegAccountLink::AssetIdRevealedElsewhere {
                    resp_participant: PartialPokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                    resp_asset_id: PartialPokDiscreteLog::deserialize_with_mode(
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
                LegAccountLink::AssetIdHidden {
                    resp_participant,
                    resp_asset_id,
                } => {
                    resp_participant.check()?;
                    resp_asset_id.check()
                }
                LegAccountLink::AssetIdRevealed { resp_participant } => resp_participant.check(),
                LegAccountLink::AssetIdRevealedElsewhere {
                    resp_participant,
                    resp_asset_id,
                } => {
                    resp_participant.check()?;
                    resp_asset_id.check()
                }
            }
        }
    }
}
