use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{vec, vec::Vec};

use super::*;

/// Mediator entry of the scheme that predates the broadcast one, where the affirmation key is
/// encrypted to a single encryption key identified by its index in [`AssetData`].
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorEncryptionV0<G: AffineRepr> {
    /// The index corresponds to the encryption key from [`AssetData`].
    pub enc_key_index: u8,
    /// Ephemeral encryption public key of the mediator.
    pub eph_pk_med_key: G,
    /// Encryption of the mediator affirmation key. Only the mediator holding the encryption key at
    /// `enc_key_index` needs to decrypt it.
    pub ct_med: G,
}

impl<G: AffineRepr> From<&MediatorEncryptionV0<G>> for MediatorEncryption<G> {
    fn from(old: &MediatorEncryptionV0<G>) -> Self {
        Self {
            eph_pk_med_keys: vec![old.eph_pk_med_key],
            ct_med: old.ct_med,
        }
    }
}

/// [`LegEncryptionCore`] without `ct_s_prime` and `ct_r_prime`.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionCoreV0<G: AffineRepr> {
    pub ct_s: G,
    pub ct_r: G,
    pub ct_amount: G,
    pub ct_asset_id: AssetIdEncryption<G>,
}

/// [`SenderEphemeralPublicKey`] without `r5`.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderEphemeralPublicKeyV0<G: AffineRepr> {
    pub r1: G,
    pub r2: Option<G>,
    pub r3: G,
    pub r4: Option<G>,
}

/// [`ReceiverEphemeralPublicKey`] without `r6`.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiverEphemeralPublicKeyV0<G: AffineRepr> {
    pub r1: Option<G>,
    pub r2: G,
    pub r3: G,
    pub r4: Option<G>,
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncCoreAndEphKeysV0<G: AffineRepr> {
    pub core: LegEncryptionCoreV0<G>,
    pub eph_pk_s: SenderEphemeralPublicKeyV0<G>,
    pub eph_pk_r: ReceiverEphemeralPublicKeyV0<G>,
}

/// Sets `ct_s_prime`, `ct_r_prime`, `eph_pk_s.r5` and `eph_pk_r.r6` to identity, which every
/// leg-link and leg-creation verifier rejects.
impl<G: AffineRepr> From<LegEncCoreAndEphKeysV0<G>> for LegEncCoreAndEphKeys<G> {
    fn from(old: LegEncCoreAndEphKeysV0<G>) -> Self {
        Self {
            core: LegEncryptionCore {
                ct_s: old.core.ct_s,
                ct_r: old.core.ct_r,
                ct_amount: old.core.ct_amount,
                ct_asset_id: old.core.ct_asset_id,
                ct_s_prime: G::zero(),
                ct_r_prime: G::zero(),
            },
            eph_pk_s: SenderEphemeralPublicKey {
                r1: old.eph_pk_s.r1,
                r2: old.eph_pk_s.r2,
                r3: old.eph_pk_s.r3,
                r4: old.eph_pk_s.r4,
                r5: G::zero(),
            },
            eph_pk_r: ReceiverEphemeralPublicKey {
                r1: old.eph_pk_r.r1,
                r2: old.eph_pk_r.r2,
                r3: old.eph_pk_r.r3,
                r4: old.eph_pk_r.r4,
                r6: G::zero(),
            },
        }
    }
}

/// Twisted Elgamal encryption of sender pk, receiver pk, amount and asset id
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionV0<G: AffineRepr> {
    pub leg_enc_core_and_eph_keys: LegEncCoreAndEphKeysV0<G>,
    /// Ephemeral public keys of auditors in the order they appear in [`AssetData`].
    pub eph_pk_enc_keys: Vec<EphemeralPublicKey<G>>,
    /// Ephemeral public keys of auditors in the order they were passed by leg creator.
    pub eph_pk_public_enc_keys: Vec<EphemeralPublicKey<G>>,
    pub mediators: Vec<MediatorEncryptionV0<G>>,
}

impl<G: AffineRepr> LegEncryptionV0<G> {
    /// Returns the asset ID of the leg, if it is revealed. Returns `None` if the asset ID is encrypted.
    pub fn asset_id(&self) -> Option<AssetId> {
        self.leg_enc_core_and_eph_keys.core.ct_asset_id.asset_id()
    }

    /// Mediator count.
    pub fn mediator_count(&self) -> usize {
        self.mediators.len()
    }
}

impl<G: AffineRepr> From<LegEncryptionV0<G>> for LegEncryption<G> {
    fn from(old: LegEncryptionV0<G>) -> Self {
        let mediators = if old.asset_id().is_some() {
            None
        } else {
            Some(old.mediators.iter().map(MediatorEncryption::from).collect())
        };
        Self {
            leg_enc_core_and_eph_keys: old.leg_enc_core_and_eph_keys.into(),
            eph_pk_enc_keys: old.eph_pk_enc_keys,
            eph_pk_public_enc_keys: old.eph_pk_public_enc_keys,
            mediators,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keys::keygen_enc;
    use ark_pallas::Affine as PallasA;
    use ark_std::UniformRand;

    #[test]
    fn v0_leg_decodes_and_converts() {
        let mut rng = rand::thread_rng();
        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);
        let (_, pk_s) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r) = keygen_enc(&mut rng, enc_key_gen);

        for reveal_asset_id in [false, true] {
            let leg = Leg::new(pk_s.0, pk_r.0, 100, 7, vec![], vec![], vec![]).unwrap();
            let config = LegEncConfig {
                visibility: PartyVisibility::FullVisibility,
                reveal_asset_id,
            };
            let (leg_enc, _) = leg.encrypt(&mut rng, config, enc_key_gen, enc_gen).unwrap();
            let LegEncCoreAndEphKeys {
                core,
                eph_pk_s,
                eph_pk_r,
            } = leg_enc.leg_enc_core_and_eph_keys.clone();
            let v0 = LegEncryptionV0 {
                leg_enc_core_and_eph_keys: LegEncCoreAndEphKeysV0 {
                    core: LegEncryptionCoreV0 {
                        ct_s: core.ct_s,
                        ct_r: core.ct_r,
                        ct_amount: core.ct_amount,
                        ct_asset_id: core.ct_asset_id.clone(),
                    },
                    eph_pk_s: SenderEphemeralPublicKeyV0 {
                        r1: eph_pk_s.r1,
                        r2: eph_pk_s.r2,
                        r3: eph_pk_s.r3,
                        r4: eph_pk_s.r4,
                    },
                    eph_pk_r: ReceiverEphemeralPublicKeyV0 {
                        r1: eph_pk_r.r1,
                        r2: eph_pk_r.r2,
                        r3: eph_pk_r.r3,
                        r4: eph_pk_r.r4,
                    },
                },
                eph_pk_enc_keys: vec![],
                eph_pk_public_enc_keys: vec![],
                mediators: vec![],
            };
            let mut bytes = Vec::new();
            v0.serialize_compressed(&mut bytes).unwrap();

            // The current layout does not decode V0 bytes.
            assert!(LegEncryption::<PallasA>::deserialize_compressed(&bytes[..]).is_err());

            let decoded = LegEncryptionV0::<PallasA>::deserialize_compressed(&bytes[..]).unwrap();
            assert_eq!(decoded, v0);
            let converted = LegEncryption::from(decoded);
            let converted_core = &converted.leg_enc_core_and_eph_keys.core;
            assert_eq!(converted_core.ct_s, core.ct_s);
            assert_eq!(converted_core.ct_amount, core.ct_amount);
            assert_eq!(converted_core.ct_asset_id, core.ct_asset_id);
            assert!(converted_core.ct_s_prime.is_zero());
            assert!(converted_core.ct_r_prime.is_zero());
            assert_eq!(converted.asset_id(), leg_enc.asset_id());
            assert_eq!(converted.mediators.is_none(), reveal_asset_id);
        }
    }
}
