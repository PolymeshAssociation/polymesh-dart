use crate::util::{
    initialize_curve_tree_prover, initialize_curve_tree_verifier, prove_with_rng, verify_with_rng,
};
use crate::util::bp_gens_for_vec_commitment;
use crate::{Error, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::iter;
use ark_std::ops::Neg;
use ark_std::{vec, vec::Vec};
use bulletproofs::BulletproofGens;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, R1CSProof, Variable};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::ped_comm_group_elems::{prove_naive, verify_naive};
use curve_tree_relations::range_proof::range_proof;
use digest::{Digest};
use dock_crypto_utils::aliases::FullDigest;
use dock_crypto_utils::concat_slices;
use dock_crypto_utils::hashing_utils::{affine_group_elem_from_try_and_incr, hash_to_field};
use dock_crypto_utils::solve_discrete_log::solve_discrete_log_bsgs_alt;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AMOUNT_BITS, AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID};
use rand_core::{CryptoRng, CryptoRngCore, RngCore};
use schnorr_pok::discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};

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
    pub fn new<D: Digest>(
        label: &[u8],
        num_keys: usize,
        leaf_layer_bp_gens: &BulletproofGens<Affine<G1>>,
    ) -> Self {
        let j_0 = affine_group_elem_from_try_and_incr::<_, D>(&concat_slices![label, b" : j_0"]);
        let comm_key = bp_gens_for_vec_commitment(num_keys + 1, leaf_layer_bp_gens).collect();
        Self { j_0, comm_key }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
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
        if params.comm_key.len() < keys.len() + 1{
            return Err(Error::InsufficientCommitmentKeyLength(params.comm_key.len(), keys.len() + 1))
        }
        // Asset id could be kept out of `points` and committed in commitment directly using one of the generators of comm_key
        // but that pushes asset id into the other group which makes the settlement txn proof quite expensive
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

    fn points(
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

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
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
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
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
    pub fn encrypt<R: CryptoRngCore, D: FullDigest>(
        &self,
        rng: &mut R,
        pk_s_enc: G,
        pk_r_enc: G,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<(LegEncryption<G>, LegEncryptionRandomness<F>)> {
        let y = F::rand(rng);

        // Optimz: Lot of the following operations can benefit from `WindowTable`
        let shared_secret = (enc_key_gen * y).into_affine();
        let (r1, r2, r3, r4) = Self::encryption_randomness::<D>(shared_secret)?;
        let ct_s = (enc_key_gen * r1 + self.pk_s).into_affine();
        let ct_r = (enc_key_gen * r2 + self.pk_r).into_affine();
        let ct_amount = (enc_key_gen * r3 + enc_gen * F::from(self.amount)).into_affine();
        let ct_asset_id = (enc_key_gen * r4 + enc_gen * F::from(self.asset_id)).into_affine();
        let eph_pk_auds_meds = self.pk_auds_meds.iter().map(|(role, pk)| {
            (*role, EphemeralPublicKey::<G>(
                (*pk * r1).into_affine(),
                (*pk * r2).into_affine(),
                (*pk * r3).into_affine(),
                (*pk * r4).into_affine(),
            ))
        });

        let eph_pk_s = (pk_s_enc * y).into_affine();
        let eph_pk_r = (pk_r_enc * y).into_affine();
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

    /// Hash `shared_secret` with counter to get `r_i`
    fn encryption_randomness<D: FullDigest>(shared_secret: G) -> Result<(F, F, F, F)> {
        let mut shared_secret_bytes = vec![];
        shared_secret.serialize_compressed(&mut shared_secret_bytes)?;
        Ok((
            hash_to_field::<F, D>(
                SK_EPH_GEN_LABEL,
                &concat_slices![&shared_secret_bytes, b":", 1_u8.to_le_bytes()],
            ),
            hash_to_field::<F, D>(
                SK_EPH_GEN_LABEL,
                &concat_slices![&shared_secret_bytes, b":", 2_u8.to_le_bytes()],
            ),
            hash_to_field::<F, D>(
                SK_EPH_GEN_LABEL,
                &concat_slices![&shared_secret_bytes, b":", 3_u8.to_le_bytes()],
            ),
            hash_to_field::<F, D>(
                SK_EPH_GEN_LABEL,
                &concat_slices![&shared_secret_bytes, b":", 4_u8.to_le_bytes()],
            ),
        ))
    }
}

impl<F: PrimeField, G: AffineRepr<ScalarField = F>> LegEncryption<G> {
    pub fn get_encryption_randomness<D: FullDigest>(
        &self,
        sk: &F,
        is_sender: bool,
    ) -> Result<LegEncryptionRandomness<F>> {
        let sk_inv = sk
            .inverse()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;
        let pk = if is_sender {
            self.eph_pk_s
        } else {
            self.eph_pk_r
        };
        let shared_secret = (pk * sk_inv).into_affine();
        let (r_1, r_2, r_3, r_4) = Leg::encryption_randomness::<D>(shared_secret)?;
        Ok(LegEncryptionRandomness(r_1, r_2, r_3, r_4))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg
    pub fn decrypt_given_r(
        &self,
        r: LegEncryptionRandomness<F>,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<(G, G, AssetId, Balance)> {
        let LegEncryptionRandomness(r_1, r_2, r_3, r_4) = r;
        let enc_key_gen = enc_key_gen.into_group();
        let enc_gen = enc_gen.into_group();
        let sender = Self::decrypt_as_group_element_given_r(&r_1, self.ct_s, enc_key_gen);
        let receiver = Self::decrypt_as_group_element_given_r(&r_2, self.ct_r, enc_key_gen);
        let amount = self.decrypt_amount_given_r(&r_3, enc_key_gen, enc_gen)?;
        let asset_id = self.decrypt_asset_id_given_r(&r_4, enc_key_gen, enc_gen)? as AssetId;
        Ok((
            sender.into_affine(),
            receiver.into_affine(),
            asset_id,
            amount,
        ))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg
    pub fn decrypt_given_key(
        &self,
        sk: &F,
        key_index: usize,
        enc_gen: G,
    ) -> Result<(G, G, AssetId, Balance)> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let sender =
            Self::decrypt_as_group_element(sk, self.ct_s, self.eph_pk_auds_meds[key_index].1.0)?;
        let receiver =
            Self::decrypt_as_group_element(sk, self.ct_r, self.eph_pk_auds_meds[key_index].1.1)?;
        let enc_gen = enc_gen.into_group();
        let asset_id = self.decrypt_asset_id(sk, key_index, enc_gen)? as AssetId;
        let amount = self.decrypt_amount(sk, key_index, enc_gen)?;
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
    ) -> Result<u64> {
        let asset_id = Self::decrypt_as_group_element_given_r(r_i, self.ct_asset_id, enc_key_gen);
        solve_discrete_log_bsgs_alt::<G::Group>(MAX_ASSET_ID as u64, enc_gen, asset_id)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `asset_id` failed.".into()))
    }

    pub fn decrypt_amount_given_r(
        &self,
        r_i: &F,
        enc_key_gen: G::Group,
        enc_gen: G::Group,
    ) -> Result<u64> {
        let amount = Self::decrypt_as_group_element_given_r(r_i, self.ct_amount, enc_key_gen);
        solve_discrete_log_bsgs_alt::<G::Group>(MAX_AMOUNT, enc_gen, amount)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))
    }

    pub fn decrypt_asset_id(&self, sk: &F, key_index: usize, enc_gen: G::Group) -> Result<u64> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let asset_id = Self::decrypt_as_group_element(
            sk,
            self.ct_asset_id,
            self.eph_pk_auds_meds[key_index].1.3,
        )?;
        solve_discrete_log_bsgs_alt::<G::Group>(MAX_ASSET_ID as u64, enc_gen, asset_id)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `asset_id` failed.".into()))
    }

    pub fn decrypt_amount(&self, sk: &F, key_index: usize, enc_gen: G::Group) -> Result<u64> {
        if key_index >= self.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let amount =
            Self::decrypt_as_group_element(sk, self.ct_amount, self.eph_pk_auds_meds[key_index].1.2)?;
        solve_discrete_log_bsgs_alt::<G::Group>(MAX_AMOUNT, enc_gen, amount)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))
    }

    pub fn decrypt_as_group_element_given_r(
        r_i: &F,
        encrypted: G,
        enc_key_gen: G::Group,
    ) -> G::Group {
        encrypted.into_group() - enc_key_gen * *r_i
    }

    pub fn decrypt_as_group_element(sk: &F, encrypted: G, eph_pk: G) -> Result<G::Group> {
        let g_k = (eph_pk
            * sk.inverse()
                .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?)
        .into_affine();
        Ok(encrypted.into_group() - g_k)
    }
}

/// Proof of knowledge of `pk` and `r_i` in `(pk * r_1, pk * r_2, pk * r_3, pk * r_4)` without revealing `pk`
/// and ensuring `pk` is the correct public key for the asset auditor/mediator
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RespEphemeralPublicKey<G: SWCurveConfig> {
    pub r_1: (Affine<G>, SchnorrResponse<Affine<G>>),
    pub r_2: PokDiscreteLog<Affine<G>>,
    pub r_3: PokDiscreteLog<Affine<G>>,
    pub r_4: PokDiscreteLog<Affine<G>>,
}

/// This is the proof for settlement creation. Report section 5.1.5
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SettlementTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G1>>,
    pub odd_proof: R1CSProof<Affine<G0>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G1, G0>,
    /// Commitment to randomness and response for proving knowledge of amount in twisted Elgamal encryption of amount.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_amount_enc: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving asset-id in twisted Elgamal encryption of asset-id.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_asset_id_enc: PokPedersenCommitment<Affine<G0>>,
    pub resp_asset_id: PokPedersenCommitment<Affine<G0>>,
    pub re_randomized_points: Vec<Affine<G0>>,
    /// Bulletproof vector commitment to `[r_1, r_2, r_3, r_4, r_2/r_1, r_3/r_1, r_4/r_1, amount]`
    pub comm_r_i_amount: Affine<G0>,
    pub t_comm_r_i_amount: Affine<G0>,
    pub resp_comm_r_i_amount: SchnorrResponse<Affine<G0>>,
    /// Response for proving correctness of ephemeral public keys. Is in the same order as the keys in [`AssetData`]
    pub resp_eph_pk_auds_meds: Vec<RespEphemeralPublicKey<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SettlementTxnProof<L, F0, F1, G0, G1>
{
    // NOTE: This pattern assumes that this is the only proof being created. But an alternative and maybe better pattern
    // is to assume that other proofs will be created along this and `Self::new` should accept transcript which are being shared
    // by other proofs. Also, this could take a randomized mult-checker which is shared by others.

    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        leaf_path: CurveTreeWitnessPath<L, G1, G0>,
        asset_data: AssetData<F0, F1, G0, G1>,
        nonce: &[u8],
        // Rest are public parameters
        tree_parameters: &SelRerandParameters<G1, G0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        if leg.asset_id != asset_data.id {
            return Err(Error::IncompatibleAssetId(leg.asset_id, asset_data.id))
        }
        let (mut even_prover, mut odd_prover, re_randomized_path, re_randomization_of_leaf) =
            initialize_curve_tree_prover(
                rng,
                SETTLE_TXN_EVEN_LABEL,
                SETTLE_TXN_ODD_LABEL,
                leaf_path,
                tree_parameters,
            );

        let mut leg_instance = vec![];
        leg_enc.serialize_compressed(&mut leg_instance)?;
        nonce.serialize_compressed(&mut leg_instance)?;
        re_randomized_path.serialize_compressed(&mut leg_instance)?;
        tree_parameters.serialize_compressed(&mut leg_instance)?;
        asset_comm_params.serialize_compressed(&mut leg_instance)?;
        enc_key_gen.serialize_compressed(&mut leg_instance)?;
        enc_gen.serialize_compressed(&mut leg_instance)?;

        odd_prover
            .transcript()
            .append_message_without_static_label(SETTLE_TXN_INSTANCE_LABEL, &leg_instance);

        let at = F0::from(leg.asset_id);
        let amount = F0::from(leg.amount);

        let rerandomized_leaf = re_randomized_path.get_rerandomized_leaf();

        let asset_data_points =
            AssetData::points(leg.asset_id, &asset_data.keys, &asset_comm_params);

        if cfg!(debug_assertions) {
            let x_coords = asset_data_points
                .clone()
                .into_iter()
                .map(|p| (tree_parameters.odd_parameters.delta + p).into_affine().x)
                .collect::<Vec<_>>();
            let commitment = G1::msm(
                &asset_comm_params.comm_key[..(asset_data_points.len())],
                x_coords.as_slice(),
            )
            .unwrap();
            assert_eq!(
                commitment
                    + (tree_parameters.even_parameters.pc_gens.B_blinding
                        * re_randomization_of_leaf),
                rerandomized_leaf.into_group()
            );
        }

        let blindings_for_points = (0..asset_data_points.len())
            .map(|_| F0::rand(rng))
            .collect::<Vec<_>>();
        let re_randomized_points = prove_naive(
            &mut even_prover,
            asset_data_points,
            &rerandomized_leaf,
            re_randomization_of_leaf,
            blindings_for_points.clone(),
            &tree_parameters.odd_parameters,
        )?;

        if cfg!(debug_assertions) {
            assert_eq!(
                re_randomized_points[0].into_group(),
                (asset_comm_params.j_0 * at)
                    + (tree_parameters.odd_parameters.pc_gens.B_blinding * blindings_for_points[0])
            );

            for i in 0..asset_data.keys.len() {
                let (r, k) = asset_data.keys[i];
                let k = if r {
                    asset_comm_params.j_0 + k
                } else {
                    k.into_group()
                };
                assert_eq!(
                    re_randomized_points[i + 1].into_group(),
                    k + (tree_parameters.odd_parameters.pc_gens.B_blinding
                        * blindings_for_points[i + 1])
                )
            }
        }

        let LegEncryptionRandomness(r_1, r_2, r_3, r_4) = leg_enc_rand;

        // Question: Does r_2 appear without any link?

        let r_1_blinding = F0::rand(rng);
        let r_2_blinding = F0::rand(rng);
        let r_3_blinding = F0::rand(rng);
        let r_4_blinding = F0::rand(rng);

        let r_1_inv = r_1.inverse().ok_or_else(|| Error::InvertingZero)?;
        let r_2_r_1_inv = r_2 * r_1_inv;
        let r_3_r_1_inv = r_3 * r_1_inv;
        let r_4_r_1_inv = r_4 * r_1_inv;
        let r_2_r_1_inv_blinding = F0::rand(rng);
        let r_3_r_1_inv_blinding = F0::rand(rng);
        let r_4_r_1_inv_blinding = F0::rand(rng);

        let amount_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);

        let comm_r_i_blinding = F0::rand(rng);
        // Commitment to `[r_1, r_2, r_3, r_4, r_2/r_1, r_3/r_1, r_4/r_1, amount]`
        let (comm_r_i_amount, vars) = odd_prover.commit_vec(&[r_1, r_2, r_3, r_4, r_2_r_1_inv, r_3_r_1_inv, r_4_r_1_inv, amount], comm_r_i_blinding, &tree_parameters.odd_parameters.bp_gens);
        Self::enforce_constraints(&mut odd_prover, Some(leg.amount), vars)?;

        let t_comm_r_i_amount = SchnorrCommitment::new(&Self::bp_gens_vec(tree_parameters), vec![
            F0::rand(rng),
            r_1_blinding,
            r_2_blinding,
            r_3_blinding,
            r_4_blinding,
            r_2_r_1_inv_blinding,
            r_3_r_1_inv_blinding,
            r_4_r_1_inv_blinding,
            amount_blinding,
        ]);

        let mut transcript = odd_prover.transcript();

        // TODO: This can be optimized by combining these. Also duplicate responses can be omitted

        let mut t_points_r1 = Vec::with_capacity(asset_data.keys.len());
        let mut t_points_r2 = Vec::with_capacity(asset_data.keys.len());
        let mut t_points_r3 = Vec::with_capacity(asset_data.keys.len());
        let mut t_points_r4 = Vec::with_capacity(asset_data.keys.len());
        let aud_role_base = asset_comm_params.j_0.neg();
        let blinding_base = tree_parameters
            .odd_parameters
            .pc_gens
            .B_blinding
            .into_group()
            .neg()
            .into_affine();
        for (i, (role, _)) in asset_data.keys.iter().enumerate() {
            let mut blindings_r1 = vec![r_1_blinding, F0::rand(rng)];
            if *role {
                blindings_r1.push(r_1_blinding);
            }
            let t_1 = if *role {
                SchnorrCommitment::new(&[
                    re_randomized_points[i + 1], // since first point commits to asset-id
                    blinding_base,
                    aud_role_base,
                ], blindings_r1)
            } else {
                SchnorrCommitment::new(&[
                    re_randomized_points[i + 1], // since first point commits to asset-id
                    blinding_base,
                ], blindings_r1)
            };

            let base = &leg_enc.eph_pk_auds_meds[i].1.0;
            let t_2 = PokDiscreteLogProtocol::init(r_2_r_1_inv, r_2_r_1_inv_blinding, base);
            let t_3 = PokDiscreteLogProtocol::init(r_3_r_1_inv, r_3_r_1_inv_blinding, base);
            let t_4 = PokDiscreteLogProtocol::init(r_4_r_1_inv, r_4_r_1_inv_blinding, base);

            t_points_r1.push(t_1);
            t_points_r2.push(t_2);
            t_points_r3.push(t_3);
            t_points_r4.push(t_4);
        }

        // Proving correctness of twisted Elgamal encryption of amount
        let t_amount_enc = PokPedersenCommitmentProtocol::init(
            r_3,
            r_3_blinding,
            &enc_key_gen,
            amount,
            amount_blinding,
            &enc_gen,
        );

        // Proving correctness of twisted Elgamal encryption of asset-id
        let t_asset_id_enc = PokPedersenCommitmentProtocol::init(
            r_4,
            r_4_blinding,
            &enc_key_gen,
            at,
            asset_id_blinding,
            &enc_gen,
        );

        // Proving correctness of asset-id in the point
        let t_asset_id = PokPedersenCommitmentProtocol::init(
            at,
            asset_id_blinding,
            &asset_comm_params.j_0,
            blindings_for_points[0],
            F0::rand(rng),
            &tree_parameters.odd_parameters.pc_gens.B_blinding,
        );

        t_comm_r_i_amount.challenge_contribution(&mut transcript)?;

        for i in 0..asset_data.keys.len() {
            re_randomized_points[i + 1].serialize_compressed(&mut transcript)?;
            t_points_r1[i].challenge_contribution(&mut transcript)?;
            let base = &leg_enc.eph_pk_auds_meds[i].1.0;
            t_points_r2[i].challenge_contribution(base, &leg_enc.eph_pk_auds_meds[i].1.1, &mut transcript)?;
            t_points_r3[i].challenge_contribution(base, &leg_enc.eph_pk_auds_meds[i].1.2, &mut transcript)?;
            t_points_r4[i].challenge_contribution(base, &leg_enc.eph_pk_auds_meds[i].1.3, &mut transcript)?;
        }

        t_amount_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_amount,
            &mut transcript,
        )?;
        t_asset_id_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_asset_id,
            &mut transcript,
        )?;
        t_asset_id.challenge_contribution(
            &asset_comm_params.j_0,
            &tree_parameters.odd_parameters.pc_gens.B_blinding,
            &re_randomized_points[0],
            &mut transcript,
        )?;

        let prover_challenge = transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        let resp_comm_r_i_amount = t_comm_r_i_amount.response(
            &[comm_r_i_blinding, r_1, r_2, r_3, r_4, r_2_r_1_inv, r_3_r_1_inv, r_4_r_1_inv, amount],
            &prover_challenge
        )?;

        let mut resp_eph_pk_auds_meds = Vec::with_capacity(asset_data.keys.len());

        for (i, ((t_points_r2, t_points_r3), t_points_r4)) in t_points_r2.into_iter().zip(t_points_r3.into_iter()).zip(t_points_r4.into_iter()).enumerate() {
            let role = asset_data.keys[i].0;

            let mut wits1 = vec![r_1, r_1 * blindings_for_points[i + 1]];
            if role {
                wits1.push(r_1);
            }
            let resp_1 = t_points_r1[i].response(&wits1, &prover_challenge)?;

            // TODO: Batch sigma can be used for these 3. And potentially these can be combined across keys. But then how to check the same response for r_2, r_3, r4?
            let resp_2 = t_points_r2.gen_proof(&prover_challenge);

            let resp_3 = t_points_r3.gen_proof(&prover_challenge);

            let resp_4 = t_points_r4.gen_proof(&prover_challenge);
            resp_eph_pk_auds_meds.push(RespEphemeralPublicKey {
                r_1: (t_points_r1[i].t, resp_1),
                r_2: resp_2,
                r_3: resp_3,
                r_4: resp_4,
            });
        }

        let resp_amount_enc = t_amount_enc.gen_proof(&prover_challenge);
        let resp_asset_id_enc = t_asset_id_enc.gen_proof(&prover_challenge);
        let resp_asset_id = t_asset_id.gen_proof(&prover_challenge);

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &tree_parameters, rng)?;

        Ok(Self {
            even_proof,
            odd_proof,
            re_randomized_path,
            resp_amount_enc,
            resp_asset_id_enc,
            resp_asset_id,
            re_randomized_points,
            comm_r_i_amount,
            t_comm_r_i_amount: t_comm_r_i_amount.t,
            resp_comm_r_i_amount,
            resp_eph_pk_auds_meds,
        })
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        // Rest are public parameters
        tree_parameters: &SelRerandParameters<G1, G0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<()> {
        if asset_comm_params.comm_key.len() < self.re_randomized_points.len() {
            return Err(Error::InsufficientCommitmentKeyLength(asset_comm_params.comm_key.len(), self.re_randomized_points.len()))
        }
        if self.re_randomized_points.len() != self.resp_eph_pk_auds_meds.len() + 1 {
            return Err(Error::DifferentNumberOfRandomizedPointsAndResponses(self.re_randomized_points.len(), self.resp_eph_pk_auds_meds.len() + 1))
        }
        if self.resp_comm_r_i_amount.len() != 9 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(9, self.resp_comm_r_i_amount.len()))
        }

        let (mut even_verifier, mut odd_verifier) = initialize_curve_tree_verifier(
            SETTLE_TXN_EVEN_LABEL,
            SETTLE_TXN_ODD_LABEL,
            self.re_randomized_path.clone(),
            tree_root,
            tree_parameters,
        );

        let mut leg_instance = vec![];
        leg_enc.serialize_compressed(&mut leg_instance)?;
        nonce.serialize_compressed(&mut leg_instance)?;
        self.re_randomized_path
            .serialize_compressed(&mut leg_instance)?;
        tree_parameters.serialize_compressed(&mut leg_instance)?;
        asset_comm_params.serialize_compressed(&mut leg_instance)?;
        enc_key_gen.serialize_compressed(&mut leg_instance)?;
        enc_gen.serialize_compressed(&mut leg_instance)?;

        odd_verifier
            .transcript()
            .append_message_without_static_label(SETTLE_TXN_INSTANCE_LABEL, &leg_instance);

        let rerandomized_leaf = self.re_randomized_path.get_rerandomized_leaf();

        verify_naive(
            &mut even_verifier,
            rerandomized_leaf,
            self.re_randomized_points.clone(),
            &tree_parameters.odd_parameters,
        )?;

        let vars = odd_verifier.commit_vec(8, self.comm_r_i_amount);
        Self::enforce_constraints(&mut odd_verifier, None, vars)?;

        let mut transcript = odd_verifier.transcript();

        self.t_comm_r_i_amount.serialize_compressed(&mut transcript)?;

        for i in 0..self.resp_eph_pk_auds_meds.len() {
            self.re_randomized_points[i + 1].serialize_compressed(&mut transcript)?;
            self.resp_eph_pk_auds_meds[i]
                .r_1
                .0
                .serialize_compressed(&mut transcript)?;
            let base = &leg_enc.eph_pk_auds_meds[i].1.0;
            self.resp_eph_pk_auds_meds[i]
                .r_2
                .challenge_contribution(base, &leg_enc.eph_pk_auds_meds[i].1.1, &mut transcript)?;
            self.resp_eph_pk_auds_meds[i]
                .r_3
                .challenge_contribution(base, &leg_enc.eph_pk_auds_meds[i].1.2, &mut transcript)?;
            self.resp_eph_pk_auds_meds[i]
                .r_4
                .challenge_contribution(base, &leg_enc.eph_pk_auds_meds[i].1.3, &mut transcript)?;
        }

        self.resp_amount_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_amount,
            &mut transcript,
        )?;
        self.resp_asset_id_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_asset_id,
            &mut transcript,
        )?;
        self.resp_asset_id.challenge_contribution(
            &asset_comm_params.j_0,
            &tree_parameters.odd_parameters.pc_gens.B_blinding,
            &self.re_randomized_points[0],
            &mut transcript,
        )?;

        let verifier_challenge = transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        if !self.resp_amount_enc.verify(
            &leg_enc.ct_amount,
            &enc_key_gen,
            &enc_gen,
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "resp_amount_enc verification failed".into(),
            ));
        }

        if self.resp_comm_r_i_amount.0[8] != self.resp_amount_enc.response2 {
            return Err(Error::ProofVerificationError(
                "Amount response mismatch".into(),
            ));
        }

        if !self.resp_asset_id.verify(
            &self.re_randomized_points[0],
            &asset_comm_params.j_0,
            &tree_parameters.odd_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "resp_asset_id verification failed".into(),
            ));
        }

        if !self.resp_asset_id_enc.verify(
            &leg_enc.ct_asset_id,
            &enc_key_gen,
            &enc_gen,
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "resp_asset_id_enc verification failed".into(),
            ));
        }

        if self.resp_asset_id.response1 != self.resp_asset_id_enc.response2 {
            return Err(Error::ProofVerificationError(
                "Assed Id response mismatch".into(),
            ));
        }

        self.resp_comm_r_i_amount.is_valid(&Self::bp_gens_vec(tree_parameters), &self.comm_r_i_amount, &self.t_comm_r_i_amount, &verifier_challenge)?;

        let aud_role_base = asset_comm_params.j_0.neg();
        let blinding_base = tree_parameters
            .odd_parameters
            .pc_gens
            .B_blinding
            .into_group()
            .neg()
            .into_affine();

        for i in 0..self.resp_eph_pk_auds_meds.len() {
            let resp = &self.resp_eph_pk_auds_meds[i];
            let role = leg_enc.eph_pk_auds_meds[i].0;
            let D_r1 = &leg_enc.eph_pk_auds_meds[i].1.0;

            if role {
                resp.r_1.1.is_valid(
                    &[
                        self.re_randomized_points[i + 1], // since first point commits to asset-id
                        blinding_base,
                        aud_role_base,
                    ],
                    D_r1,
                    &resp.r_1.0,
                    &verifier_challenge,
                )?;
                if resp.r_1.1.0[0] != resp.r_1.1.0[2] {
                    return Err(Error::ProofVerificationError(
                        "Mismatch in response for r_1".into(),
                    ));
                }
            } else {
                resp.r_1.1.is_valid(
                    &[
                        self.re_randomized_points[i + 1], // since first point commits to asset-id
                        blinding_base,
                    ],
                    D_r1,
                    &resp.r_1.0,
                    &verifier_challenge,
                )?;
            }

            if !resp.r_2.verify(
                &leg_enc.eph_pk_auds_meds[i].1.1,
                D_r1,
                &verifier_challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    format!("resp_leaf_points[{i}].r_2 verification mismatch"),
                ));
            }
            if !resp.r_3.verify(
                &leg_enc.eph_pk_auds_meds[i].1.2,
                D_r1,
                &verifier_challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    format!("resp_leaf_points[{i}].r_3 verification mismatch"),
                ));
            }
            if !resp.r_4.verify(
                &leg_enc.eph_pk_auds_meds[i].1.3,
                D_r1,
                &verifier_challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    format!("resp_leaf_points[{i}].r_4 verification mismatch"),
                ));
            }

            if resp.r_1.1.0[0] != self.resp_comm_r_i_amount.0[1] {
                return Err(Error::ProofVerificationError(
                    "Mismatch in response for r_1".into(),
                ));
            }
            if resp.r_2.response != self.resp_comm_r_i_amount.0[5] {
                return Err(Error::ProofVerificationError(
                    "Mismatch in response for r_2/r_1".into(),
                ));
            }
            if resp.r_3.response != self.resp_comm_r_i_amount.0[6] {
                return Err(Error::ProofVerificationError(
                    "Mismatch in response for r_3/r_1".into(),
                ));
            }
            if resp.r_4.response != self.resp_comm_r_i_amount.0[7] {
                return Err(Error::ProofVerificationError(
                    "Mismatch in response for r_4/r_1".into(),
                ));
            }
        }

        verify_with_rng(
            even_verifier,
            odd_verifier,
            &self.even_proof,
            &self.odd_proof,
            &tree_parameters,
            rng,
        )?;
        Ok(())
    }

    pub(crate) fn enforce_constraints<CS: ConstraintSystem<F0>>(
        cs: &mut CS,
        amount: Option<Balance>,
        mut committed_variables: Vec<Variable<F0>>,
    ) -> Result<()> {
        let var_r_1 = committed_variables.remove(0);
        let var_r_2 = committed_variables.remove(0);
        let var_r_3 = committed_variables.remove(0);
        let var_r_4 = committed_variables.remove(0);
        let var_r_2_r_1_inv = committed_variables.remove(0);
        let var_r_3_r_1_inv = committed_variables.remove(0);
        let var_r_4_r_1_inv = committed_variables.remove(0);
        let var_amount = committed_variables.remove(0);

        let lc_r_1: LinearCombination<_> = var_r_1.into();
        let (_, _, var_r_2_) = cs.multiply(lc_r_1.clone(), var_r_2_r_1_inv.into());
        let (_, _, var_r_3_) = cs.multiply(lc_r_1.clone(), var_r_3_r_1_inv.into());
        let (_, _, var_r_4_) = cs.multiply(lc_r_1.clone(), var_r_4_r_1_inv.into());
        cs.constrain(var_r_2 - var_r_2_);
        cs.constrain(var_r_3 - var_r_3_);
        cs.constrain(var_r_4 - var_r_4_);

        // TODO: What if we do range proof outside circuit? Or using another protocol like Bulletproofs++?
        range_proof(
            cs,
            var_amount.into(),
            amount,
            AMOUNT_BITS.into(),
        )?;
        Ok(())
    }

    pub(crate)fn bp_gens_vec(account_tree_params: &SelRerandParameters<G1, G0>) -> [Affine<G0>; 9] {
        let mut gens = bp_gens_for_vec_commitment(8, &account_tree_params.odd_parameters.bp_gens);
        [
            account_tree_params.odd_parameters.pc_gens.B_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ]
    }
}

/// This is the proof for mediator affirm/reject. Report section 5.1.12
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorTxnProof<G: AffineRepr> {
    pub resp_enc_pk: PokPedersenCommitment<G>,
}

impl<G: AffineRepr> MediatorTxnProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        asset_id: AssetId,
        mediator_sk: G::ScalarField,
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

        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let D = leg_enc.eph_pk_auds_meds[index_in_asset_data].1.3;
        let minus_h = enc_gen.into_group().neg().into_affine();
        let enc_pk = PokPedersenCommitmentProtocol::init(
            mediator_sk,
            G::ScalarField::rand(rng),
            &leg_enc.ct_asset_id,
            mediator_sk * G::ScalarField::from(asset_id),
            G::ScalarField::rand(rng),
            &minus_h,
        );

        enc_pk.challenge_contribution(&leg_enc.ct_asset_id, &minus_h, &D, &mut transcript)?;

        let mut extra_instance = vec![];
        leg_enc.serialize_compressed(&mut extra_instance)?;
        index_in_asset_data.serialize_compressed(&mut extra_instance)?;
        nonce.serialize_compressed(&mut extra_instance)?;
        enc_gen.serialize_compressed(&mut extra_instance)?;

        transcript
            .append_message_without_static_label(MEDIATOR_TXN_INSTANCE_LABEL, &extra_instance);

        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

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

        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let D = leg_enc.eph_pk_auds_meds[index_in_asset_data].1.3;
        let minus_h = enc_gen.into_group().neg().into_affine();

        self.resp_enc_pk.challenge_contribution(
            &leg_enc.ct_asset_id,
            &minus_h,
            &D,
            &mut transcript,
        )?;

        let mut extra_instance = vec![];
        leg_enc.serialize_compressed(&mut extra_instance)?;
        index_in_asset_data.serialize_compressed(&mut extra_instance)?;
        nonce.serialize_compressed(&mut extra_instance)?;
        enc_gen.serialize_compressed(&mut extra_instance)?;

        transcript
            .append_message_without_static_label(MEDIATOR_TXN_INSTANCE_LABEL, &extra_instance);

        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

        if !self
            .resp_enc_pk
            .verify(&D, &leg_enc.ct_asset_id, &minus_h, &challenge)
        {
            return Err(Error::ProofVerificationError(
                "resp_enc_pk verification failed".into(),
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc, keygen_sig};
    use ark_ec::VariableBaseMSM;
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
    use rand_core::CryptoRngCore;
    use std::time::Instant;
    use crate::account_registration::tests::setup_comm_key;
    use crate::account::AccountCommitmentKeyTrait;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type PallasFr = ark_pallas::Fr;

    /// Generate account signing and encryption keys for all sender, receiver, and auditor.
    /// This is just for testing and in practice, each party generates its own keys.
    pub fn setup_keys<R: CryptoRngCore, G: AffineRepr>(
        rng: &mut R,
        sig_key_gen: G,
        enc_key_gen: G,
    ) -> (
        ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
        ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
        ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
    ) {
        // Account signing (affirmation) keys
        let (sk_s, pk_s) = keygen_sig(rng, sig_key_gen);
        let (sk_r, pk_r) = keygen_sig(rng, sig_key_gen);
        let (sk_a, pk_a) = keygen_sig(rng, sig_key_gen);

        // Encryption keys
        let (sk_s_e, pk_s_e) = keygen_enc(rng, enc_key_gen);
        let (sk_r_e, pk_r_e) = keygen_enc(rng, enc_key_gen);
        let (sk_a_e, pk_a_e) = keygen_enc(rng, enc_key_gen);
        (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        )
    }

    #[test]
    fn leg_verification() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;

        // Create public params (generators, etc)
        let asset_tree_params =
            SelRerandParameters::<VestaParameters, PallasParameters>::new(NUM_GENS, NUM_GENS)
                .unwrap();

        let sig_key_gen = PallasA::rand(&mut rng);
        let enc_key_gen = PallasA::rand(&mut rng);
        // Called h in report
        let enc_gen = PallasA::rand(&mut rng);

        let num_auditors = 2;
        let num_mediators = 3;
        let asset_id = 1;

        let asset_comm_params =
            AssetCommitmentParams::<PallasParameters, VestaParameters>::new::<Blake2b512>(
                b"asset-comm-params",
                num_auditors + num_mediators,
                &asset_tree_params.even_parameters.bp_gens,
            );

        // Account signing (affirmation) keys
        let (sk_s, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (sk_r, pk_r) = keygen_sig(&mut rng, sig_key_gen);

        // Encryption keys
        let (sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_auditor = (0..num_auditors)
            .map(|_| {
                (
                    keygen_sig(&mut rng, sig_key_gen),
                    keygen_enc(&mut rng, enc_key_gen),
                )
            })
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| {
                (
                    keygen_sig(&mut rng, sig_key_gen),
                    keygen_enc(&mut rng, enc_key_gen),
                )
            })
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity(num_auditors + num_mediators);
        keys.extend(
            keys_auditor
                .iter()
                .map(|(_, (_, k))| (true, k.0))
                .into_iter(),
        );
        keys.extend(
            keys_mediator
                .iter()
                .map(|(_, (_, k))| (false, k.0))
                .into_iter(),
        );
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        ).unwrap();

        // Check asset_data is correctly constructed
        let points = AssetData::points(asset_id, &asset_data.keys, &asset_comm_params);
        assert_eq!(points[0], asset_comm_params.j_0 * PallasFr::from(asset_id));
        for i in 0..num_auditors {
            assert_eq!(
                points[i + 1].into_group(),
                asset_comm_params.j_0 + keys_auditor[i].1.1.0
            );
        }
        for i in 0..num_mediators {
            assert_eq!(
                points[i + 1 + num_auditors].into_group(),
                keys_mediator[i].1.1.0
            );
        }

        let x_coords = points
            .into_iter()
            .map(|p| (asset_tree_params.odd_parameters.delta + p).into_affine().x)
            .collect::<Vec<_>>();
        let expected_commitment = ark_vesta::Projective::msm(
            &asset_comm_params.comm_key[..(num_auditors + num_mediators + 1)],
            x_coords.as_slice(),
        )
        .unwrap();
        assert_eq!(expected_commitment, asset_data.commitment.into_group());

        let set = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set,
            &asset_tree_params,
            Some(2),
        );

        let amount = 100;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let leg = Leg::new(
            pk_s.0,
            pk_r.0,
            keys.clone(),
            amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Venue gets the leaf path from the tree
        let path = asset_tree.get_path_to_leaf_for_proof(0, 0);

        let proof = SettlementTxnProof::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            path,
            asset_data.clone(),
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        // Verifier gets the root of the tree
        let root = asset_tree.root_node();

        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        let r = leg_enc
            .get_encryption_randomness::<Blake2b512>(&sk_s_e.0, true)
            .unwrap();
        assert_eq!(r.0, leg_enc_rand.0);
        assert_eq!(r.1, leg_enc_rand.1);
        assert_eq!(r.2, leg_enc_rand.2);
        assert_eq!(r.3, leg_enc_rand.3);

        let (p1, p2, a, b) = leg_enc.decrypt_given_r(r, enc_key_gen, enc_gen).unwrap();
        assert_eq!(p1, pk_s.0);
        assert_eq!(p2, pk_r.0);
        assert_eq!(a, asset_id);
        assert_eq!(b, amount);

        let mut index = 0;
        for (_, (d, _)) in keys_auditor.into_iter().chain(keys_mediator.into_iter()) {
            let (p1, p2, a, b) = leg_enc.decrypt_given_key(&d.0, index, enc_gen).unwrap();
            assert_eq!(p1, pk_s.0);
            assert_eq!(p2, pk_r.0);
            assert_eq!(a, asset_id);
            assert_eq!(b, amount);
            index += 1;
        }

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn mediator_action() {
        let mut rng = rand::thread_rng();

        // TODO: Generate by hashing public string
        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);
        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);


        // Account signing (affirmation) keys
        let (sk_s, pk_s) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_r, pk_r) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        // Encryption keys
        let (sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let num_auditors = 2;
        let num_mediators = 3;
        let keys_auditor = (0..num_auditors)
            .map(|_| {
                (
                    keygen_sig(&mut rng, account_comm_key.sk_gen()),
                    keygen_enc(&mut rng, enc_key_gen),
                )
            })
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| {
                (
                    keygen_sig(&mut rng, account_comm_key.sk_gen()),
                    keygen_enc(&mut rng, enc_key_gen),
                )
            })
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity(num_auditors + num_mediators);
        keys.extend(
            keys_auditor
                .iter()
                .map(|(_, (s, k))| (true, k.0, s.0))
                .into_iter(),
        );
        keys.extend(
            keys_mediator
                .iter()
                .map(|(_, (s, k))| (false, k.0, s.0))
                .into_iter(),
        );



        // Venue has successfully created the settlement and leg commitment has been stored on chain
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

        log::info!("proof size = {}", proof.compressed_size());
        log::info!(
            "prover time = {:?}, verifier time = {:?}",
            prover_time,
            verifier_time
        );

        match proof.verify(leg_enc.clone(), accept, 10, nonce, enc_gen).err().unwrap() {
            Error::InvalidKeyIndex(i) => assert_eq!(i, 10),
            _ => panic!("Didn't error but should have"),
        }

        match proof.verify(leg_enc.clone(), accept, 0, nonce, enc_gen).err().unwrap() {
            Error::MediatorNotFoundAtIndex(i) => assert_eq!(i, 0),
            _ => panic!("Didn't error but should have"),
        }
    }
}
