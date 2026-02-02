pub mod mediator;
pub mod proofs;

#[cfg(test)]
pub mod tests;

use core::iter;
use crate::util::{bp_gens_for_vec_commitment};
use crate::{error::Result, Error};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{vec, vec::Vec};
use polymesh_dart_common::{AssetId, Balance, MAX_ASSET_ID, MAX_BALANCE};
use rand_core::CryptoRngCore;
use zeroize::{Zeroize, ZeroizeOnDrop};
use dock_crypto_utils::aliases::FullDigest;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use ark_pallas::PallasConfig;
use bulletproofs::BulletproofGens;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use digest::Digest;
use dock_crypto_utils::hashing_utils::affine_group_elem_from_try_and_incr;
use dock_crypto_utils::concat_slices;
use crate::discrete_log::solve_discrete_log_bsgs;
pub use self::mediator::MediatorTxnProof;
pub use self::proofs::{LegCreationProof, SettlementCreationProof};

pub const LEG_TXN_ODD_LABEL: &[u8; 17] = b"leg-txn-odd-level";
pub const LEG_TXN_EVEN_LABEL: &[u8; 18] = b"leg-txn-even-level";
pub const LEG_TXN_CHALLENGE_LABEL: &[u8; 17] = b"leg-txn-challenge";
pub const LEG_TXN_INSTANCE_LABEL: &[u8; 22] = b"leg-txn-extra-instance";
pub const SK_EPH_GEN_LABEL: &[u8; 20] = b"ephemeral-secret-key";

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AssetCommitmentParams<
    G0: SWCurveConfig + Clone + Copy,
    G1: SWCurveConfig<ScalarField = G0::BaseField, BaseField = G0::ScalarField> + Clone + Copy,
> {
    pub j_0: Affine<G0>,
    pub comm_key: Vec<Affine<G1>>,
}

impl<
    G0: SWCurveConfig + Clone + Copy,
    G1: SWCurveConfig<ScalarField = G0::BaseField, BaseField = G0::ScalarField> + Clone + Copy,
> AssetCommitmentParams<G0, G1>
{
    /// Need the same generators as used in Bulletproofs of the curve tree system because the verifier "commits" to the x-coordinates using the same key
    /// Use try-and-increment
    pub fn new_deprecated<D: Digest>(
        label: &[u8],
        num_keys: u32,
        leaf_layer_bp_gens: &BulletproofGens<Affine<G1>>,
    ) -> Self {
        let j_0 = affine_group_elem_from_try_and_incr::<_, D>(&concat_slices![label, b" : j_0"]);
        let comm_key = bp_gens_for_vec_commitment(num_keys + 1, leaf_layer_bp_gens).collect();
        Self { j_0, comm_key }
    }
}

impl<
    G1: SWCurveConfig<
        ScalarField = <PallasConfig as CurveConfig>::BaseField,
        BaseField = <PallasConfig as CurveConfig>::ScalarField,
    > + Clone
    + Copy,
> AssetCommitmentParams<PallasConfig, G1>
{
    /// Need the same generators as used in Bulletproofs of the curve tree system because the verifier "commits" to the x-coordinates using the same key
    pub fn new(
        label: &[u8],
        num_keys: u32,
        leaf_layer_bp_gens: &BulletproofGens<Affine<G1>>,
    ) -> Self {
        let j_0 = hash_to_pallas(label, b" : j_0").into_affine();
        let comm_key = bp_gens_for_vec_commitment(num_keys + 1, leaf_layer_bp_gens).collect();
        Self { j_0, comm_key }
    }
}

#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct AssetData<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub id: AssetId,
    /// if role is auditor, then boolean = true else false
    pub keys: Vec<(bool, Affine<G0>)>,
    /// A non-hiding commitment to asset-id and keys
    pub commitment: Affine<G1>,
}

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AssetData<F0, F1, G0, G1>
{
    pub fn new(
        id: AssetId,
        keys: Vec<(bool, Affine<G0>)>,
        params: &AssetCommitmentParams<G0, G1>,
        delta: Affine<G0>,
    ) -> Result<Self> {
        if params.comm_key.len() < keys.len() + 1 {
            return Err(Error::InsufficientCommitmentKeyLength(
                params.comm_key.len(),
                keys.len() + 1,
            ));
        }
        // Asset id could be kept out of `points` and committed in commitment directly using one of the generators of comm_key
        // but that pushes asset id into the other group which makes the leg creation txn proof quite expensive
        let points = Self::points(id, &keys, params);
        let x_coords = points
            .into_iter()
            .map(|p| (delta + p).into_affine().x)
            .collect::<Vec<_>>();
        let commitment =
            G1::msm(&params.comm_key[..(keys.len() + 1)], x_coords.as_slice()).unwrap();
        Ok(Self {
            id,
            keys,
            commitment: commitment.into_affine(),
        })
    }

    /// Return 1 point per key and role combined. The idea is to have 1 point per auditor/mediator and the
    /// point should encapsulate all info about that auditor/mediator
    pub fn points(
        asset_id: AssetId,
        keys: &[(bool, Affine<G0>)],
        params: &AssetCommitmentParams<G0, G1>,
    ) -> Vec<Affine<G0>> {
        iter::once((params.j_0 * G0::ScalarField::from(asset_id)).into_affine())
            .chain(keys.iter().map(|(role, k)| {
                let role = if *role {
                    params.j_0
                } else {
                    Affine::<G0>::zero()
                };
                (role + *k).into_affine()
            }))
            .collect()
    }

    // More efficient update methods can be added in future
}

#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct Leg<G: AffineRepr> {
    /// Public key of sender
    pub pk_s: G,
    /// Public key of receiver
    pub pk_r: G,
    /// Public keys of auditors and mediators in the order they appear in [`AssetData`].
    /// If role is auditor, then boolean = true else false
    pub pk_auds_meds: Vec<(bool, G)>,
    pub amount: Balance,
    pub asset_id: AssetId,
}

/// Twisted Elgamal's ephemeral public key per auditor/mediator `(pk * r_1, pk * r_2, pk * r_3, pk * r_4)`
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EphemeralPublicKey<G: AffineRepr>(pub G, pub G, pub G, pub G);

/// (r_1, r_2, r_3, r_4)
#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct LegEncryptionRandomness<F: PrimeField>(pub F, pub F, pub F, pub F);

/// Twisted Elgamal encryption of sender, receiver public keys, amount and asset id for all the auditors and mediators
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryption<G: AffineRepr> {
    pub ct_s: G,
    pub ct_r: G,
    pub ct_amount: G,
    pub ct_asset_id: G,
    /// Used by sender to recover `r_i`
    pub eph_pk_s: G,
    /// Used by receiver to recover `r_i`
    pub eph_pk_r: G,
    /// Ephemeral public keys of auditors and mediators in the order they appear in [`AssetData`].
    /// If role is auditor, then boolean = true else false
    pub eph_pk_auds_meds: Vec<(bool, EphemeralPublicKey<G>)>,
}

impl<F: PrimeField, G: AffineRepr<ScalarField = F>> Leg<G> {
    /// Its assumed that caller ensures that no duplicate keys are passed for
    /// auditors and mediators else the proofs will be more expensive than they need to be.
    /// Also assumes that all keys are passed and in the same order as in [`AssetData`]
    pub fn new(
        pk_s: G,
        pk_r: G,
        pk_auds_meds: Vec<(bool, G)>,
        amount: Balance,
        asset_id: AssetId,
    ) -> Result<Self> {
        if amount > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount));
        }
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }
        Ok(Self {
            pk_s,
            pk_r,
            pk_auds_meds,
            amount,
            asset_id,
        })
    }

    /// Report calls `enc_key_gen` as `g` and `enc_gen` as `h`
    pub fn encrypt<R: CryptoRngCore, D: FullDigest>(
        &self,
        rng: &mut R,
        pk_s_enc: G,
        pk_r_enc: G,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<(LegEncryption<G>, LegEncryptionRandomness<F>)> {
        let mut y = F::rand(rng);

        let mut amount = F::from(self.amount);
        let mut asset_id = F::from(self.asset_id);

        // Optimz: Lot of the following operations can benefit from `WindowTable`
        let shared_secret = (enc_key_gen * y).into_affine();
        let (r1, r2, r3, r4) = Self::encryption_randomness::<D>(shared_secret)?;
        let ct_s = (enc_key_gen * r1 + self.pk_s).into_affine();
        let ct_r = (enc_key_gen * r2 + self.pk_r).into_affine();
        let ct_amount = (enc_key_gen * r3 + enc_gen * amount).into_affine();
        let ct_asset_id = (enc_key_gen * r4 + enc_gen * asset_id).into_affine();
        let eph_pk_auds_meds = self.pk_auds_meds.iter().map(|(role, pk)| {
            (
                *role,
                EphemeralPublicKey::<G>(
                    (*pk * r1).into_affine(),
                    (*pk * r2).into_affine(),
                    (*pk * r3).into_affine(),
                    (*pk * r4).into_affine(),
                ),
            )
        });

        let eph_pk_s = (pk_s_enc * y).into_affine();
        let eph_pk_r = (pk_r_enc * y).into_affine();

        Zeroize::zeroize(&mut amount);
        Zeroize::zeroize(&mut asset_id);
        Zeroize::zeroize(&mut y);

        Ok((
            LegEncryption {
                ct_s,
                ct_r,
                ct_amount,
                ct_asset_id,
                eph_pk_s,
                eph_pk_r,
                eph_pk_auds_meds: eph_pk_auds_meds.collect(),
            },
            LegEncryptionRandomness(r1, r2, r3, r4),
        ))
    }

    /// Hash `shared_secret` to get `r_i`
    pub fn encryption_randomness<D: FullDigest>(mut shared_secret: G) -> Result<(F, F, F, F)> {
        let mut shared_secret_bytes = vec![];
        shared_secret.serialize_compressed(&mut shared_secret_bytes)?;

        let hasher = <DefaultFieldHasher<D> as HashToField<F>>::new(SK_EPH_GEN_LABEL);
        let r = hasher.hash_to_field::<4>(&shared_secret_bytes);

        Zeroize::zeroize(&mut shared_secret);
        Zeroize::zeroize(&mut shared_secret_bytes);

        let [r_1, r_2, r_3, r_4] = r;

        Ok((r_1, r_2, r_3, r_4))
    }
}

impl<F: PrimeField, G: AffineRepr<ScalarField = F>> LegEncryption<G> {
    pub fn get_encryption_randomness<D: FullDigest>(
        &self,
        sk: &F,
        is_sender: bool,
    ) -> Result<LegEncryptionRandomness<F>> {
        let mut sk_inv = sk
            .inverse()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;
        let pk = if is_sender {
            self.eph_pk_s
        } else {
            self.eph_pk_r
        };
        let shared_secret = (pk * sk_inv).into_affine();

        Zeroize::zeroize(&mut sk_inv);

        let (r_1, r_2, r_3, r_4) = Leg::encryption_randomness::<D>(shared_secret)?;
        Ok(LegEncryptionRandomness(r_1, r_2, r_3, r_4))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given r_i
    pub fn decrypt_given_r(
        &self,
        r: LegEncryptionRandomness<F>,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<(G, G, AssetId, Balance)> {
        self.decrypt_given_r_with_limits(r, enc_key_gen, enc_gen, None, None)
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given r_i
    pub fn decrypt_given_r_with_limits(
        &self,
        r: LegEncryptionRandomness<F>,
        enc_key_gen: G,
        enc_gen: G,
        max_asset_id: Option<AssetId>,
        max_amount: Option<Balance>,
    ) -> Result<(G, G, AssetId, Balance)> {
        let LegEncryptionRandomness(mut r_1, mut r_2, mut r_3, mut r_4) = r;
        let enc_key_gen = enc_key_gen.into_group();
        let enc_gen = enc_gen.into_group();
        let max_asset_id = max_asset_id.unwrap_or(MAX_ASSET_ID);
        let max_amount = max_amount.unwrap_or(MAX_BALANCE);

        // Decrypt asset-id first as they will fail quickly if the wrong `r_i` is used.
        let asset_id =
            self.decrypt_asset_id_given_r(&r_4, enc_key_gen, enc_gen, max_asset_id)? as AssetId;
        let amount = self.decrypt_amount_given_r(&r_3, enc_key_gen, enc_gen, max_amount)?;

        let sender = Self::decrypt_as_group_element_given_r(&r_1, self.ct_s, enc_key_gen);
        let receiver = Self::decrypt_as_group_element_given_r(&r_2, self.ct_r, enc_key_gen);

        Zeroize::zeroize(&mut r_1);
        Zeroize::zeroize(&mut r_2);
        Zeroize::zeroize(&mut r_3);
        Zeroize::zeroize(&mut r_4);

        Ok((
            sender.into_affine(),
            receiver.into_affine(),
            asset_id,
            amount,
        ))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given r_i
    pub fn decrypt_given_r_checked(
        &self,
        r: LegEncryptionRandomness<F>,
        enc_key_gen: G,
        enc_gen: G,
        pk: G,
        is_sender: bool,
    ) -> Result<(G, G, AssetId, Balance)> {
        let LegEncryptionRandomness(mut r_1, mut r_2, mut r_3, mut r_4) = r;
        let enc_key_gen = enc_key_gen.into_group();

        // Check that decrypted sender/receiver matches `pk`
        let (sender, receiver) = if is_sender {
            let sender =
                Self::decrypt_as_group_element_given_r(&r_1, self.ct_s, enc_key_gen).into_affine();
            if pk != sender {
                return Err(Error::DecryptionFailed(
                    "Decrypted sender pk does not match".into(),
                ));
            }
            let receiver =
                Self::decrypt_as_group_element_given_r(&r_2, self.ct_r, enc_key_gen).into_affine();
            (sender, receiver)
        } else {
            let receiver =
                Self::decrypt_as_group_element_given_r(&r_2, self.ct_r, enc_key_gen).into_affine();
            if pk != receiver {
                return Err(Error::DecryptionFailed(
                    "Decrypted receiver pk does not match".into(),
                ));
            }
            let sender =
                Self::decrypt_as_group_element_given_r(&r_1, self.ct_s, enc_key_gen).into_affine();
            (sender, receiver)
        };

        let enc_gen = enc_gen.into_group();
        let asset_id =
            self.decrypt_asset_id_given_r(&r_4, enc_key_gen, enc_gen, MAX_ASSET_ID)? as AssetId;
        let amount = self.decrypt_amount_given_r(&r_3, enc_key_gen, enc_gen, MAX_BALANCE)?;

        Zeroize::zeroize(&mut r_1);
        Zeroize::zeroize(&mut r_2);
        Zeroize::zeroize(&mut r_3);
        Zeroize::zeroize(&mut r_4);

        Ok((sender, receiver, asset_id, amount))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given decryption key of auditor/mediator.
    /// `key_index` is the index of auditor/mediator key in [`AssetData`]
    pub fn decrypt_given_key(
        &self,
        sk: &F,
        key_index: usize,
        enc_gen: G,
    ) -> Result<(G, G, AssetId, Balance)> {
        self.decrypt_given_key_with_limits(sk, key_index, enc_gen, None, None)
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given decryption key of auditor/mediator.
    /// `key_index` is the index of auditor/mediator key in [`AssetData`]
    pub fn decrypt_given_key_with_limits(
        &self,
        sk: &F,
        key_index: usize,
        enc_gen: G,
        max_asset_id: Option<AssetId>,
        max_amount: Option<Balance>,
    ) -> Result<(G, G, AssetId, Balance)> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let max_asset_id = max_asset_id.unwrap_or(MAX_ASSET_ID);
        let max_amount = max_amount.unwrap_or(MAX_BALANCE);

        // Compute inverse of secret key once.
        let mut sk_inv = sk
            .inverse()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;

        // Try to decrypt asset-id and amount first as they will fail if the wrong secret key is used.
        let enc_gen = enc_gen.into_group();
        let asset_id = self.decrypt_asset_id(&sk_inv, key_index, enc_gen, max_asset_id)? as AssetId;
        let amount = self.decrypt_amount(&sk_inv, key_index, enc_gen, max_amount)?;

        let sender = Self::decrypt_as_group_element(
            &sk_inv,
            self.ct_s,
            self.eph_pk_auds_meds[key_index].1.0,
        );
        let receiver = Self::decrypt_as_group_element(
            &sk_inv,
            self.ct_r,
            self.eph_pk_auds_meds[key_index].1.1,
        );

        Zeroize::zeroize(&mut sk_inv);

        Ok((
            sender.into_affine(),
            receiver.into_affine(),
            asset_id,
            amount,
        ))
    }

    pub fn decrypt_asset_id_given_r(
        &self,
        r_i: &F,
        enc_key_gen: G::Group,
        enc_gen: G::Group,
        max_asset_id: AssetId,
    ) -> Result<u64> {
        let asset_id = Self::decrypt_as_group_element_given_r(r_i, self.ct_asset_id, enc_key_gen);

        solve_discrete_log_bsgs::<G::Group>(max_asset_id as u64, enc_gen, asset_id)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `asset_id` failed.".into()))
    }

    pub fn decrypt_amount_given_r(
        &self,
        r_i: &F,
        enc_key_gen: G::Group,
        enc_gen: G::Group,
        max_amount: Balance,
    ) -> Result<u64> {
        let amount = Self::decrypt_as_group_element_given_r(r_i, self.ct_amount, enc_key_gen);

        solve_discrete_log_bsgs::<G::Group>(max_amount, enc_gen, amount)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))
    }

    pub fn decrypt_asset_id(
        &self,
        sk_inv: &F,
        key_index: usize,
        enc_gen: G::Group,
        max_asset_id: AssetId,
    ) -> Result<u64> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let asset_id = Self::decrypt_as_group_element(
            sk_inv,
            self.ct_asset_id,
            self.eph_pk_auds_meds[key_index].1.3,
        );

        solve_discrete_log_bsgs::<G::Group>(max_asset_id as _, enc_gen, asset_id)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `asset_id` failed.".into()))
    }

    pub fn decrypt_amount(
        &self,
        sk_inv: &F,
        key_index: usize,
        enc_gen: G::Group,
        max_amount: Balance,
    ) -> Result<u64> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let amount = Self::decrypt_as_group_element(
            sk_inv,
            self.ct_amount,
            self.eph_pk_auds_meds[key_index].1.2,
        );

        solve_discrete_log_bsgs::<G::Group>(max_amount, enc_gen, amount)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))
    }

    pub fn decrypt_as_group_element_given_r(
        r_i: &F,
        encrypted: G,
        enc_key_gen: G::Group,
    ) -> G::Group {
        encrypted.into_group() - enc_key_gen * r_i
    }

    pub fn decrypt_as_group_element(sk_inv: &F, encrypted: G, eph_pk: G) -> G::Group {
        encrypted.into_group() - eph_pk * sk_inv
    }
}

