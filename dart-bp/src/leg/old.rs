use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{vec, vec::Vec};

use super::*;

/// Mediator entry of the scheme that predates the broadcast one, where the affirmation key is
/// encrypted to a single encryption key identified by its index in [`AssetData`]. Kept so legs
/// created under that scheme can still be affirmed, using [`crate::leg::mediator::MediatorTxnOldProof`].
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

/// Twisted Elgamal encryption of sender pk, receiver pk, amount and asset id
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionV0<G: AffineRepr> {
    pub leg_enc_core_and_eph_keys: LegEncCoreAndEphKeys<G>,
    /// Ephemeral public keys of auditors in the order they appear in [`AssetData`].
    pub eph_pk_enc_keys: Vec<EphemeralPublicKey<G>>,
    /// Ephemeral public keys of auditors in the order they were passed by leg creator.
    pub eph_pk_public_enc_keys: Vec<EphemeralPublicKey<G>>,
    pub mediators: Vec<MediatorEncryptionV0<G>>,
}

impl<G: AffineRepr> From<LegEncryptionV0<G>> for LegEncryption<G> {
    fn from(old: LegEncryptionV0<G>) -> Self {
        let mediators = if old.leg_enc_core_and_eph_keys.core.is_asset_id_revealed() {
            None
        } else {
            Some(old.mediators.iter().map(MediatorEncryption::from).collect())
        };
        Self {
            leg_enc_core_and_eph_keys: old.leg_enc_core_and_eph_keys,
            eph_pk_enc_keys: old.eph_pk_enc_keys,
            eph_pk_public_enc_keys: old.eph_pk_public_enc_keys,
            mediators,
        }
    }
}
