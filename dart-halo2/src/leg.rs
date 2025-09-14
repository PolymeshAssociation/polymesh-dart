use std::iter;
use ct_halo2::tree::prover::SelectAndRerandomizePath;
use ff::PrimeField;

use rand_core::CryptoRngCore;
use crate::AffineSerializable;
use zkcrypto_utils::solve_discrete_log::solve_discrete_log_bsgs_alt;
use polymesh_dart_common::{AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID};
use crate::error::{Error, Result};
use crate::utils::TranscriptWriter;
use digest::{Digest, DynDigest};
use group::Curve;
use group::prime::PrimeCurveAffine;
use multiexp::multiexp_vartime;
use sigma_protocols::discrete_log::{PokPedersenCommitment, PokPedersenCommitmentProtocol};
use zkcrypto_utils::hash_to_field::{DefaultFieldHasher, HashToField};
use zkcrypto_utils::hashing_utils::affine_group_elem_from_try_and_incr;
use crate::types_and_constants::TXN_CHALLENGE_LABEL;

/// Concatenates supplied slices into one continuous vector.
#[macro_export]
macro_rules! concat_slices {
    ($($slice: expr),+) => {
        [$(&$slice[..]),+].concat()
    }
}

pub const SETTLE_TXN_ODD_LABEL: &[u8; 24] = b"settlement-txn-odd-level";
pub const SETTLE_TXN_EVEN_LABEL: &[u8; 25] = b"settlement-txn-even-level";
pub const SETTLE_TXN_CHALLENGE_LABEL: &[u8; 24] = b"settlement-txn-challenge";
pub const SETTLE_TXN_INSTANCE_LABEL: &[u8; 29] = b"settlement-txn-extra-instance";

pub const SK_EPH_GEN_LABEL: &[u8; 20] = b"ephemeral-secret-key";
pub const MEDIATOR_TXN_LABEL: &[u8; 12] = b"mediator-txn";
pub const MEDIATOR_TXN_RESPONSE_LABEL: &[u8; 17] = b"mediator-response";
pub const MEDIATOR_TXN_ACCEPT_RESPONSE: &[u8; 6] = b"accept";
pub const MEDIATOR_TXN_REJECT_RESPONSE: &[u8; 6] = b"reject";
pub const MEDIATOR_TXN_CHALLENGE_LABEL: &[u8; 22] = b"mediator-txn-challenge";
pub const MEDIATOR_TXN_INSTANCE_LABEL: &[u8; 27] = b"mediator-txn-extra-instance";

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Leg<C: AffineSerializable> {
    /// Public key of sender
    pub pk_s: C,
    /// Public key of receiver
    pub pk_r: C,
    /// Public keys of auditors and mediators in the order they appear in [`AssetData`].
    /// If role is auditor, then boolean = true else false
    pub pk_auds_meds: Vec<(bool, C)>,
    pub amount: Balance,
    pub asset_id: AssetId,
}

/// Twisted Elgamal's ephemeral public key per auditor/mediator `(pk * r_1, pk * r_2, pk * r_3, pk * r_4)`
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct EphemeralPublicKey<C: AffineSerializable>(pub C, pub C, pub C, pub C);

/// (r_1, r_2, r_3, r_4)
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LegEncryptionRandomness<F: PrimeField>(pub F, pub F, pub F, pub F);

/// Twisted Elgamal encryption of sender, receiver public keys, amount and asset id for all the auditors and mediators
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LegEncryption<C: AffineSerializable> {
    pub ct_s: C,
    pub ct_r: C,
    pub ct_amount: C,
    pub ct_asset_id: C,
    /// Used by sender to recover `r_i`
    pub eph_pk_s: C,
    /// Used by receiver to recover `r_i`
    pub eph_pk_r: C,
    /// Ephemeral public keys of auditors and mediators in the order they appear in [`AssetData`].
    /// If role is auditor, then boolean = true else false
    pub eph_pk_auds_meds: Vec<(bool, EphemeralPublicKey<C>)>,
}

impl<F: PrimeField, C: AffineSerializable<ScalarExt = F>> Leg<C> {
    /// Its assumed that caller ensures that no duplicate keys are passed for
    /// auditors and mediators else the proofs will be more expensive than they need to be.
    /// Also assumes that all keys are passed and in the same order as in [`AssetData`]
    pub fn new(
        pk_s: C,
        pk_r: C,
        pk_auds_meds: Vec<(bool, C)>,
        amount: Balance,
        asset_id: AssetId,
    ) -> Result<Self> {
        if amount > MAX_AMOUNT {
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
    pub fn encrypt<R: CryptoRngCore, D: Default + DynDigest + Clone>(
        &self,
        rng: &mut R,
        pk_s_enc: C,
        pk_r_enc: C,
        enc_key_gen: C,
        enc_gen: C,
    ) -> Result<(LegEncryption<C>, LegEncryptionRandomness<F>)>
    {
        let y = F::random(rng);

        // Optimz: Lot of the following operations can benefit from `WindowTable`
        let shared_secret = (enc_key_gen * y).to_affine();
        let (r1, r2, r3, r4) = Self::encryption_randomness::<D>(shared_secret)?;
        let ct_s = (enc_key_gen * r1 + self.pk_s).into();
        let ct_r = (enc_key_gen * r2 + self.pk_r).into();
        let ct_amount = (enc_key_gen * r3 + enc_gen * F::from(self.amount)).into();
        let ct_asset_id = (enc_key_gen * r4 + enc_gen * F::from(self.asset_id.into())).into();
        let eph_pk_auds_meds = self.pk_auds_meds.iter().map(|(role, pk)| {
            (*role, EphemeralPublicKey(
                (*pk * r1).into(),
                (*pk * r2).into(),
                (*pk * r3).into(),
                (*pk * r4).into(),
            ))
        });

        let eph_pk_s = (pk_s_enc * y).into();
        let eph_pk_r = (pk_r_enc * y).into();
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
    fn encryption_randomness<D: Default + DynDigest + Clone>(shared_secret: C) -> Result<(F, F, F, F)> {
        let shared_secret_bytes = shared_secret.to_bytes();

        let hasher = <DefaultFieldHasher<D> as HashToField<F>>::new(SK_EPH_GEN_LABEL);
        let mut r = hasher.hash_to_field(shared_secret_bytes.as_ref(), 4);

        Ok((
            r.remove(0),
            r.remove(0),
            r.remove(0),
            r.remove(0)
        ))
    }
}

impl<F: PrimeField, C: AffineSerializable<ScalarExt = F>> LegEncryption<C> {
    pub fn get_encryption_randomness<D: Default + DynDigest + Clone>(
        &self,
        sk: &F,
        is_sender: bool,
    ) -> Result<LegEncryptionRandomness<F>>
    {
        let sk_inv = sk
            .invert()
            .into_option()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;
        let pk = if is_sender {
            self.eph_pk_s
        } else {
            self.eph_pk_r
        };
        let shared_secret = (pk * sk_inv).to_affine();
        let (r_1, r_2, r_3, r_4) = Leg::encryption_randomness::<D>(shared_secret)?;
        Ok(LegEncryptionRandomness(r_1, r_2, r_3, r_4))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given r_i
    pub fn decrypt_given_r(
        &self,
        r: LegEncryptionRandomness<F>,
        enc_key_gen: C,
        enc_gen: C,
    ) -> Result<(C, C, AssetId, Balance)> {
        let LegEncryptionRandomness(r_1, r_2, r_3, r_4) = r;
        let enc_key_gen = enc_key_gen.to_curve();
        let enc_gen = enc_gen.to_curve();
        let sender = Self::decrypt_as_group_element_given_r(&r_1, self.ct_s, enc_key_gen);
        let receiver = Self::decrypt_as_group_element_given_r(&r_2, self.ct_r, enc_key_gen);
        let amount = self.decrypt_amount_given_r(&r_3, enc_key_gen, enc_gen)?;
        let asset_id = self.decrypt_asset_id_given_r(&r_4, enc_key_gen, enc_gen)? as AssetId;
        Ok((
            sender.into(),
            receiver.into(),
            asset_id,
            amount,
        ))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given decryption key of auditor/mediator
    /// `key_index` is the index of auditor/mediator key in [`AssetData`]
    pub fn decrypt_given_key(
        &self,
        sk: &F,
        key_index: usize,
        enc_gen: C,
    ) -> Result<(C, C, AssetId, Balance)> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let sender =
            Self::decrypt_as_group_element(sk, self.ct_s, self.eph_pk_auds_meds[key_index].1.0)?;
        let receiver =
            Self::decrypt_as_group_element(sk, self.ct_r, self.eph_pk_auds_meds[key_index].1.1)?;
        let enc_gen = enc_gen.to_curve();
        let asset_id = self.decrypt_asset_id(sk, key_index, enc_gen)? as AssetId;
        let amount = self.decrypt_amount(sk, key_index, enc_gen)?;
        Ok((
            sender.into(),
            receiver.into(),
            asset_id,
            amount,
        ))
    }

    pub fn decrypt_asset_id_given_r(
        &self,
        r_i: &F,
        enc_key_gen: C::CurveExt,
        enc_gen: C::CurveExt,
    ) -> Result<u64> {
        let asset_id = Self::decrypt_as_group_element_given_r(r_i, self.ct_asset_id, enc_key_gen);
        solve_discrete_log_bsgs_alt::<C::CurveExt>(MAX_ASSET_ID as u64, enc_gen, asset_id)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `asset_id` failed.".into()))
    }

    pub fn decrypt_amount_given_r(
        &self,
        r_i: &F,
        enc_key_gen: C::CurveExt,
        enc_gen: C::CurveExt,
    ) -> Result<u64> {
        let amount = Self::decrypt_as_group_element_given_r(r_i, self.ct_amount, enc_key_gen);
        solve_discrete_log_bsgs_alt::<C::Curve>(MAX_AMOUNT, enc_gen, amount)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))
    }

    pub fn decrypt_asset_id(&self, sk: &F, key_index: usize, enc_gen: C::CurveExt) -> Result<u64> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let asset_id = Self::decrypt_as_group_element(
            sk,
            self.ct_asset_id,
            self.eph_pk_auds_meds[key_index].1.3,
        )?;
        solve_discrete_log_bsgs_alt::<C::Curve>(MAX_ASSET_ID as u64, enc_gen, asset_id)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `asset_id` failed.".into()))
    }

    pub fn decrypt_amount(&self, sk: &F, key_index: usize, enc_gen: C::CurveExt) -> Result<u64> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let amount =
            Self::decrypt_as_group_element(sk, self.ct_amount, self.eph_pk_auds_meds[key_index].1.2)?;
        solve_discrete_log_bsgs_alt::<C::Curve>(MAX_AMOUNT, enc_gen, amount)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))
    }

    pub fn decrypt_as_group_element_given_r(
        r_i: &F,
        encrypted: C,
        enc_key_gen: C::Curve,
    ) -> C::Curve {
        encrypted.to_curve() - enc_key_gen * *r_i
    }

    pub fn decrypt_as_group_element(sk: &F, encrypted: C, eph_pk: C) -> Result<C::Curve> {
        let sk_inv = sk.invert().into_option().ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;
        let g_k = eph_pk * sk_inv;
        Ok(encrypted.to_curve() - g_k)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssetCommitmentParams<
    G0: AffineSerializable,
    G1: AffineSerializable<Base = G0::ScalarExt, ScalarExt = G0::Base>,
> {
    pub j_0: G0,
    pub comm_key: Vec<G1>,
}

impl<
    G0: AffineSerializable,
    G1: AffineSerializable<Base = G0::ScalarExt, ScalarExt = G0::Base>,
> AssetCommitmentParams<G0, G1> {
    /// Need the same generators as used in Bulletproofs of the curve tree system because the verifier "commits" to the x-coordinates using the same key
    pub fn new<D: Digest>(
        label: &[u8],
        num_keys: usize,
        leaf_layer_halo2_column_ck: &[G1],
    ) -> Self {
        // TODO: Fix
        let j_0 = G0::generator();
        // let j_0 = affine_group_elem_from_try_and_incr::<G0, D>(&concat_slices![label, b" : j_0"]);
        let comm_key = leaf_layer_halo2_column_ck[..num_keys].to_vec();
        Self { j_0, comm_key }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssetData<
    G0: AffineSerializable,
    G1: AffineSerializable<Base = G0::ScalarExt, ScalarExt = G0::Base>,
> {
    pub id: AssetId,
    /// if role is auditor, then boolean = true else false
    pub keys: Vec<(bool, G0)>,
    /// A non-hiding commitment to asset-id and keys
    pub commitment: G1,
}

impl<
    G0: AffineSerializable,
    G1: AffineSerializable<Base = G0::ScalarExt, ScalarExt = G0::Base>,
> AssetData<G0, G1> {
    pub fn new(
        id: AssetId,
        keys: Vec<(bool, G0)>,
        params: &AssetCommitmentParams<G0, G1>,
        delta: G0,
    ) -> Result<Self> {
        if params.comm_key.len() < keys.len() + 1{
            return Err(Error::InsufficientCommitmentKeyLength(params.comm_key.len(), keys.len() + 1))
        }
        // Asset id could be kept out of `points` and committed in commitment directly using one of the generators of comm_key
        // but that pushes asset id into the other group which makes the settlement txn proof quite expensive
        let points = Self::points(id, &keys, params);
        let mut pairs = vec![];
        for (i, p) in points.into_iter().enumerate() {
            let xy = (delta + p).to_affine().coordinates().unwrap();
            let x = xy.x();
            pairs.push((*x, params.comm_key[i].to_curve()));
        }
        let commitment = multiexp_vartime(&pairs).to_affine();
        Ok(Self {
            id,
            keys,
            commitment,
        })
    }

    /// Return 1 point per key and role combined. The idea is to have 1 point per auditor/mediator and the
    /// point should encapsulate all info about that auditor/mediator
    fn points(
        asset_id: AssetId,
        keys: &[(bool, G0)],
        params: &AssetCommitmentParams<G0, G1>,
    ) -> Vec<G0> {
        iter::once((params.j_0 * G0::Scalar::from(asset_id as u64)).to_affine())
            .chain(keys.iter().map(|(role, k)| {
                let role = if *role {
                    params.j_0
                } else {
                    G0::identity()
                };
                (role + *k).to_affine()
            }))
            .collect()
    }

    // More efficient update methods can be added in future
}

#[derive(Clone, Debug)]
pub struct SettlementCreationProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> {
    pub re_randomized_path: SelectAndRerandomizePath<G0, G1, L>,
    pub snark_proof_even: Vec<u8>,
    pub snark_proof_odd: Vec<u8>,
}

/// Mediator transaction proof using Pedersen commitment proof of knowledge
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MediatorTxnProof<G: AffineSerializable> {
    pub resp_enc_pk: PokPedersenCommitment<G>,
}

impl<F: PrimeField, G: AffineSerializable<ScalarExt = F>> MediatorTxnProof<G>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        asset_id: AssetId,
        mediator_sk: F,
        accept: bool,
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
    ) -> Result<Self> {
        if index_in_asset_data >= leg_enc.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(index_in_asset_data));
        }
        // Role should be false for mediator
        if leg_enc.eph_pk_auds_meds[index_in_asset_data].0 {
            return Err(Error::MediatorNotFoundAtIndex(index_in_asset_data));
        }

        let mut transcript = merlin::Transcript::new(MEDIATOR_TXN_LABEL);

        let mut extra_instance = vec![];
        // TODO: Implement serialization for LegEncryption
        extra_instance.extend_from_slice(&index_in_asset_data.to_le_bytes());
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(enc_gen.to_bytes().as_ref());

        transcript.append_message(MEDIATOR_TXN_INSTANCE_LABEL, &extra_instance);

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let D = leg_enc.eph_pk_auds_meds[index_in_asset_data].1.3;

        let minus_h = -enc_gen;

        let enc_pk = PokPedersenCommitmentProtocol::init(
            mediator_sk,
            F::random(&mut *rng),
            &leg_enc.ct_asset_id,
            mediator_sk * F::from(asset_id.into()),
            F::random(&mut *rng),
            &minus_h,
        );

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        enc_pk.challenge_contribution(&leg_enc.ct_asset_id, &minus_h, &D, &mut transcript_writer)?;

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let resp_enc_pk = enc_pk.gen_proof(&challenge);
        Ok(Self { resp_enc_pk })
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G>,
        accept: bool,
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
    ) -> Result<()> {
        if index_in_asset_data >= leg_enc.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(index_in_asset_data));
        }
        // Role should be false for mediator
        if leg_enc.eph_pk_auds_meds[index_in_asset_data].0 {
            return Err(Error::MediatorNotFoundAtIndex(index_in_asset_data));
        }

        let mut transcript = merlin::Transcript::new(MEDIATOR_TXN_LABEL);

        let mut extra_instance = vec![];
        // TODO: Implement serialization for LegEncryption
        extra_instance.extend_from_slice(&index_in_asset_data.to_le_bytes());
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(enc_gen.to_bytes().as_ref());

        transcript.append_message(MEDIATOR_TXN_INSTANCE_LABEL, &extra_instance);

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let d_point = leg_enc.eph_pk_auds_meds[index_in_asset_data].1.3;
        let minus_h = -enc_gen;

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        self.resp_enc_pk.challenge_contribution(
            &leg_enc.ct_asset_id,
            &minus_h,
            &d_point,
            &mut transcript_writer,
        )?;

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        self.resp_enc_pk
            .verify(&d_point, &leg_enc.ct_asset_id, &minus_h, &challenge)
            .map_err(|_| Error::ProofVerificationError(
                "resp_enc_pk verification failed".into(),
            ))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use pasta_curves::{pallas, vesta};
    use rand_core::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use blake2::Blake2b512;
    use ct_halo2::tree::tree::CurveTree;
    use group::{Curve, Group};
    use pasta_curves::arithmetic::CurveAffine;
    use crate::{keygen_enc};
    use crate::account::tests::setup_keys;
    use crate::circuits::leg::tests::{generate_vesta_sel_rerand_params, setup_curve_tree_params_for_leg_creation};
    use crate::circuits::mint::tests::generate_pallas_sel_rerand_params;

    type PallasAffine = pallas::Affine;
    type VestaAffine = vesta::Affine;

    #[test]
    fn leg_verification() {
        let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

        let sig_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        // Account signing (affirmation) and encryption keys
        let send_recv_keys = setup_keys(&mut rng, sig_key_gen, enc_key_gen);
        let ((_, pk_s), (sk_s_e, pk_s_e)) = send_recv_keys.0;
        let ((_, pk_r), (sk_r_e, pk_r_e)) = send_recv_keys.1;

        let asset_id = 1;
        let amount = 100;

        let num_auditors = 2;
        let num_mediators = 3;

        let k = 11;
        const L: usize = 1024;
        let height = 2;
        const NUM_KEYS_PLUS_1: usize = 6;
        assert_eq!(NUM_KEYS_PLUS_1, num_auditors + num_mediators + 1);

        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_leg_creation::<L, NUM_KEYS_PLUS_1>(k, height);

        let asset_comm_params =
            AssetCommitmentParams::<PallasAffine, VestaAffine>::new::<Blake2b512>(
                b"asset-comm-params",
                num_auditors + num_mediators,
                &circuit_params.even.g_lagrange,
            );

        let (sr_params, sr_proving_params, sr_verifying_params) = generate_vesta_sel_rerand_params::<L>();

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity(num_auditors + num_mediators);
        keys.extend(
            keys_auditor
                .iter()
                .map(|(_, k)| (true, k.0))
                .into_iter(),
        );
        keys.extend(
            keys_mediator
                .iter()
                .map(|(_, k)| (false, k.0))
                .into_iter(),
        );

        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            sr_proving_params.odd_level_delta,
        )
            .unwrap();
        let asset_tree = CurveTree::<VestaAffine, PallasAffine, L>::from_leaves(
            &[asset_data.commitment],
            &sr_params,
            Some(height),
        );

        // Check asset_data is correctly constructed
        let points = AssetData::points(asset_id, &asset_data.keys, &asset_comm_params);
        assert_eq!(points[0], (asset_comm_params.j_0 * pallas::Scalar::from(asset_id as u64)).to_affine());
        for i in 0..num_auditors {
            assert_eq!(
                points[i + 1],
                (asset_comm_params.j_0 + keys_auditor[i].1.0).to_affine()
            );
        }
        for i in 0..num_mediators {
            assert_eq!(
                points[i + 1 + num_auditors],
                keys_mediator[i].1.0
            );
        }

        let mut pairs = vec![];
        for (i, p) in points.into_iter().enumerate() {
            let xy = (sr_proving_params.odd_level_delta + p).to_affine().coordinates().unwrap();
            let x = xy.x();
            pairs.push((*x, asset_comm_params.comm_key[i].to_curve()));
        }
        let expected_commitment = multiexp_vartime(&pairs).to_affine();
        assert_eq!(expected_commitment, asset_data.commitment);

        let amount = 100;

        let nonce = b"test-nonce";

        // Create leg
        let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let _r = leg_enc
            .get_encryption_randomness::<Blake2b512>(&sk_r_e.0, false)
            .unwrap();
        assert_eq!(_r.0, leg_enc_rand.0);
        assert_eq!(_r.1, leg_enc_rand.1);
        assert_eq!(_r.2, leg_enc_rand.2);
        assert_eq!(_r.3, leg_enc_rand.3);

        let r = leg_enc
            .get_encryption_randomness::<Blake2b512>(&sk_s_e.0, true)
            .unwrap();
        assert_eq!(r.0, leg_enc_rand.0);
        assert_eq!(r.1, leg_enc_rand.1);
        assert_eq!(r.2, leg_enc_rand.2);
        assert_eq!(r.3, leg_enc_rand.3);

        // Test decryption with recovered randomness
        let (decrypted_pk_s, decrypted_pk_r, decrypted_asset_id, decrypted_amount) = 
            leg_enc.decrypt_given_r(r, enc_key_gen, enc_gen).unwrap();
        
        assert_eq!(decrypted_pk_s, pk_s.0);
        assert_eq!(decrypted_pk_r, pk_r.0);
        assert_eq!(decrypted_asset_id, asset_id);
        assert_eq!(decrypted_amount, amount);

        // Test decryption with keys for each auditor and mediator
        for (index, (d, _)) in keys_auditor.into_iter().chain(keys_mediator.into_iter()).enumerate() {
            let (p1, p2, a, b) = leg_enc.decrypt_given_key(&d.0, index, enc_gen).unwrap();
            assert_eq!(p1, pk_s.0);
            assert_eq!(p2, pk_r.0);
            assert_eq!(a, asset_id);
            assert_eq!(b, amount);
        }
    }

    #[test]
    fn mediator_action() {
        use std::time::Instant;

        let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

        let sig_key_gen: pallas::Affine = pallas::Point::random(&mut rng).into();
        let enc_key_gen: pallas::Affine = pallas::Point::random(&mut rng).into();
        let enc_gen: pallas::Affine = pallas::Point::random(&mut rng).into();

        // Use setup_keys to generate all the keys
        let send_recv_keys = setup_keys(&mut rng, sig_key_gen, enc_key_gen);
        let ((_, pk_s), (_, pk_s_e)) = send_recv_keys.0;
        let ((_, pk_r), (_, pk_r_e)) = send_recv_keys.1;

        let asset_id = 1;
        let amount = 100;

        let num_auditors = 2;
        let num_mediators = 3;

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity(num_auditors + num_mediators);
        keys.extend(
            keys_auditor
                .iter()
                .map(|(s, k)| (true, k.0, s.0))
                .into_iter(),
        );
        keys.extend(
            keys_mediator
                .iter()
                .map(|(s, k)| (false, k.0, s.0))
                .into_iter(),
        );

        let leg = Leg::new(pk_s.0, pk_r.0, keys.clone().into_iter().map(|(role, k, _)| (role, k)).collect(), amount, asset_id).unwrap();
        let (leg_enc, _) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let nonce = b"test-nonce";

        // Mediator "accept"ing in this case
        let accept = true;

        // Choosing second mediator
        let mediator_index_in_keys = num_auditors + 2;

        let clock = Instant::now();
        let proof = MediatorTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            asset_id,
            keys[mediator_index_in_keys].2,
            accept,
            mediator_index_in_keys,
            nonce,
            enc_gen,
        ).unwrap();
        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof.verify(leg_enc.clone(), accept, mediator_index_in_keys, nonce, enc_gen).unwrap();

        let verifier_time = clock.elapsed();

        println!("prover time = {:?}, verifier time = {:?}", prover_time, verifier_time);

        // Test error cases
        match proof.verify(leg_enc.clone(), accept, 10, nonce, enc_gen) {
            Err(Error::InvalidKeyIndex(i)) => assert_eq!(i, 10),
            _ => panic!("Expected InvalidKeyIndex error"),
        }

        match proof.verify(leg_enc.clone(), accept, 0, nonce, enc_gen) {
            Err(Error::MediatorNotFoundAtIndex(i)) => assert_eq!(i, 0),
            _ => panic!("Expected MediatorNotFoundAtIndex error"),
        }
    }
}
