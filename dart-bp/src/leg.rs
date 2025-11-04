use crate::util::bp_gens_for_vec_commitment;
use crate::util::{
    BPProof, add_verification_tuples_to_rmc, get_verification_tuples_with_rng, prove_with_rng,
    verify_given_verification_tuples,
};
use crate::{Error, ROOT_LABEL, add_to_transcript, error::Result};
use crate::{LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::PrimeField;
use ark_ff::field_hashers::{DefaultFieldHasher, HashToField};
use ark_pallas::PallasConfig;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::format;
use ark_std::iter;
use ark_std::ops::Neg;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::BulletproofGens;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use bulletproofs::r1cs::{
    ConstraintSystem, LinearCombination, Prover, Variable, VerificationTuple, Verifier,
};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::ped_comm_group_elems::{prove_naive, verify_naive};
use curve_tree_relations::range_proof::range_proof;
use digest::Digest;
use dock_crypto_utils::aliases::FullDigest;
use dock_crypto_utils::concat_slices;
use dock_crypto_utils::hashing_utils::affine_group_elem_from_try_and_incr;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::solve_discrete_log::solve_discrete_log_bsgs_alt;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, BALANCE_BITS, Balance, MAX_ASSET_ID, MAX_BALANCE};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::{Zeroize, ZeroizeOnDrop};

pub const SETTLE_TXN_ODD_LABEL: &[u8; 24] = b"settlement-txn-odd-level";
pub const SETTLE_TXN_EVEN_LABEL: &[u8; 25] = b"settlement-txn-even-level";
pub const SETTLE_TXN_CHALLENGE_LABEL: &[u8; 24] = b"settlement-txn-challenge";
pub const SETTLE_TXN_INSTANCE_LABEL: &[u8; 29] = b"settlement-txn-extra-instance";
pub const INDEX_IN_ASSET_DATA_LABEL: &'static [u8; 19] = b"index_in_asset_data";

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

    /// Return 1 point per key and role combined. The idea is to have 1 point per auditor/mediator and the
    /// point should encapsulate all info about that auditor/mediator
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
    fn encryption_randomness<D: FullDigest>(mut shared_secret: G) -> Result<(F, F, F, F)> {
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

        solve_discrete_log_bsgs_alt::<G::Group>(max_asset_id as u64, enc_gen, asset_id)
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

        solve_discrete_log_bsgs_alt::<G::Group>(max_amount, enc_gen, amount)
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

        solve_discrete_log_bsgs_alt::<G::Group>(max_asset_id as _, enc_gen, asset_id)
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

        solve_discrete_log_bsgs_alt::<G::Group>(max_amount, enc_gen, amount)
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

/// Proof of knowledge of `pk` and `r_i` in `(pk * r_1, pk * r_2, pk * r_3, pk * r_4)` without revealing `pk`
/// and ensuring `pk` is the correct public key for the asset auditor/mediator
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RespEphemeralPublicKey<G: SWCurveConfig> {
    pub r_1: Partial2PokPedersenCommitment<Affine<G>>,
    pub r_2: PartialPokDiscreteLog<Affine<G>>,
    pub r_3: PartialPokDiscreteLog<Affine<G>>,
    pub r_4: PartialPokDiscreteLog<Affine<G>>,
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
    /// When this is None, external [`R1CSProof`] will be used and [`SettlementTxnProof`] only
    /// contains proof for the sigma protocols and enforces the Bulletproof constraints.
    pub r1cs_proof: Option<BPProof<G1, G0>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G1, G0>,
    /// Commitment to randomness and response for proving knowledge of amount in twisted Elgamal encryption of amount.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_amount_enc: PartialPokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving asset-id in twisted Elgamal encryption of asset-id.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_asset_id_enc: PartialPokPedersenCommitment<Affine<G0>>,
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
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        leaf_path: CurveTreeWitnessPath<L, G1, G0>,
        asset_data: AssetData<F0, F1, G0, G1>,
        tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        // Rest are public parameters
        tree_parameters: &SelRerandParameters<G1, G0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let even_transcript = MerlinTranscript::new(SETTLE_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(SETTLE_TXN_ODD_LABEL);
        let mut even_prover =
            Prover::new(&tree_parameters.even_parameters.pc_gens, even_transcript);
        let mut odd_prover = Prover::new(&tree_parameters.odd_parameters.pc_gens, odd_transcript);
        let mut proof = Self::new_with_given_prover(
            rng,
            leg,
            leg_enc,
            leg_enc_rand,
            leaf_path,
            asset_data,
            tree_root,
            nonce,
            tree_parameters,
            asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )?;

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &tree_parameters, rng)?;

        proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });
        Ok(proof)
    }

    pub fn new_with_given_prover<R: CryptoRngCore>(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        leaf_path: CurveTreeWitnessPath<L, G1, G0>,
        asset_data: AssetData<F0, F1, G0, G1>,
        tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        // Rest are public parameters
        tree_parameters: &SelRerandParameters<G1, G0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    ) -> Result<Self> {
        ensure_proper_leg_creation(&leg, &leg_enc, &asset_data)?;
        // TODO: This is suboptimal if the same root is being used since the same children (of root) are being allocated each time this is called.
        let (re_randomized_path, mut re_randomization_of_leaf) = leaf_path
            .select_and_rerandomize_prover_gadget(even_prover, odd_prover, tree_parameters, rng);

        add_to_transcript!(
            odd_prover.transcript(),
            ROOT_LABEL,
            tree_root,
            LEG_ENC_LABEL,
            leg_enc,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path
        );

        let mut at = F0::from(leg.asset_id);
        let mut amount = F0::from(leg.amount);

        let rerandomized_leaf = re_randomized_path.get_rerandomized_leaf();

        let num_asset_data_keys = asset_data.keys.len();

        let asset_data_points =
            AssetData::points(leg.asset_id, &asset_data.keys, &asset_comm_params);

        let num_asset_data_points = asset_data_points.len();

        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if cfg!(debug_assertions) {
            let x_coords = asset_data_points
                .clone()
                .into_iter()
                .map(|p| (tree_parameters.odd_parameters.delta + p).into_affine().x)
                .collect::<Vec<_>>();
            let commitment = G1::msm(
                &asset_comm_params.comm_key[..num_asset_data_points],
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

        let mut blindings_for_points = (0..num_asset_data_points)
            .map(|_| F0::rand(rng))
            .collect::<Vec<_>>();
        let re_randomized_points = prove_naive(
            even_prover,
            asset_data_points,
            &rerandomized_leaf,
            re_randomization_of_leaf,
            blindings_for_points.clone(),
            &tree_parameters.odd_parameters,
        )?;

        Zeroize::zeroize(&mut re_randomization_of_leaf);

        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if cfg!(debug_assertions) {
            assert_eq!(
                re_randomized_points[0].into_group(),
                (asset_comm_params.j_0 * at)
                    + (tree_parameters.odd_parameters.pc_gens.B_blinding * blindings_for_points[0])
            );

            for i in 0..num_asset_data_keys {
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

        let LegEncryptionRandomness(mut r_1, mut r_2, mut r_3, mut r_4) = leg_enc_rand;

        // Question: Does r_2 appear without any link?. Maybe I use similar relation for r_2 as r_1 and use the optimization for r_3 and r_4.
        // Because if proof for r_2 can be forged then venue can make the receiver public key unrecoverable for auditor

        let mut r_1_blinding = F0::rand(rng);
        let mut r_2_blinding = F0::rand(rng);
        let mut r_3_blinding = F0::rand(rng);
        let mut r_4_blinding = F0::rand(rng);

        let mut r_1_inv = r_1.inverse().ok_or_else(|| Error::InvertingZero)?;
        let mut r_2_r_1_inv = r_2 * r_1_inv;
        let mut r_3_r_1_inv = r_3 * r_1_inv;
        let mut r_4_r_1_inv = r_4 * r_1_inv;
        let mut r_2_r_1_inv_blinding = F0::rand(rng);
        let mut r_3_r_1_inv_blinding = F0::rand(rng);
        let mut r_4_r_1_inv_blinding = F0::rand(rng);

        Zeroize::zeroize(&mut r_1_inv);

        let mut amount_blinding = F0::rand(rng);
        let mut asset_id_blinding = F0::rand(rng);

        let mut comm_r_i_blinding = F0::rand(rng);
        let mut wits = [
            r_1,
            r_2,
            r_3,
            r_4,
            r_2_r_1_inv,
            r_3_r_1_inv,
            r_4_r_1_inv,
            amount,
        ];
        // Commitment to `[r_1, r_2, r_3, r_4, r_2/r_1, r_3/r_1, r_4/r_1, amount]`
        let (comm_r_i_amount, vars) = odd_prover.commit_vec(
            &wits,
            comm_r_i_blinding,
            &tree_parameters.odd_parameters.bp_gens,
        );
        Self::enforce_constraints(odd_prover, Some(leg.amount), vars)?;

        Zeroize::zeroize(&mut wits);

        // Sigma protocol for proving knowledge of `comm_r_i_amount`
        let t_comm_r_i_amount = SchnorrCommitment::new(
            &Self::bp_gens_vec(tree_parameters),
            vec![
                F0::rand(rng),
                r_1_blinding,
                r_2_blinding,
                r_3_blinding,
                r_4_blinding,
                r_2_r_1_inv_blinding,
                r_3_r_1_inv_blinding,
                r_4_r_1_inv_blinding,
                amount_blinding,
            ],
        );

        let mut transcript = odd_prover.transcript();

        // TODO: This can be optimized by combining these.

        let mut r_1_protocol_base1 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r1 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r2 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r3 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r4 = Vec::with_capacity(num_asset_data_keys);
        let aud_role_base = asset_comm_params.j_0.neg();
        let blinding_base = tree_parameters
            .odd_parameters
            .pc_gens
            .B_blinding
            .into_group()
            .neg()
            .into_affine();
        for (i, (role, _)) in asset_data.keys.iter().enumerate() {
            let base1 = if *role {
                (re_randomized_points[i + 1] + aud_role_base).into_affine()
            } else {
                re_randomized_points[i + 1]
            };
            let t_1 = PokPedersenCommitmentProtocol::init(
                r_1,
                r_1_blinding,
                &base1,
                r_1 * blindings_for_points[i + 1],
                F0::rand(rng),
                &blinding_base,
            );
            r_1_protocol_base1.push(base1);

            let base = &leg_enc.eph_pk_auds_meds[i].1.0;
            let t_2 = PokDiscreteLogProtocol::init(r_2_r_1_inv, r_2_r_1_inv_blinding, base);
            let t_3 = PokDiscreteLogProtocol::init(r_3_r_1_inv, r_3_r_1_inv_blinding, base);
            let t_4 = PokDiscreteLogProtocol::init(r_4_r_1_inv, r_4_r_1_inv_blinding, base);

            t_points_r1.push(t_1);
            t_points_r2.push(t_2);
            t_points_r3.push(t_3);
            t_points_r4.push(t_4);
        }

        Zeroize::zeroize(&mut r_1_blinding);
        Zeroize::zeroize(&mut r_2_blinding);
        Zeroize::zeroize(&mut r_2_r_1_inv_blinding);
        Zeroize::zeroize(&mut r_3_r_1_inv_blinding);
        Zeroize::zeroize(&mut r_4_r_1_inv_blinding);

        // Proving correctness of twisted Elgamal encryption of amount
        let t_amount_enc = PokPedersenCommitmentProtocol::init(
            r_3,
            r_3_blinding,
            &enc_key_gen,
            amount,
            amount_blinding,
            &enc_gen,
        );
        Zeroize::zeroize(&mut r_3_blinding);
        Zeroize::zeroize(&mut amount_blinding);

        // Proving correctness of twisted Elgamal encryption of asset-id
        let t_asset_id_enc = PokPedersenCommitmentProtocol::init(
            r_4,
            r_4_blinding,
            &enc_key_gen,
            at,
            asset_id_blinding,
            &enc_gen,
        );
        Zeroize::zeroize(&mut r_4_blinding);

        // Proving correctness of asset-id in the point
        let t_asset_id = PokPedersenCommitmentProtocol::init(
            at,
            asset_id_blinding,
            &asset_comm_params.j_0,
            blindings_for_points[0],
            F0::rand(rng),
            &tree_parameters.odd_parameters.pc_gens.B_blinding,
        );
        Zeroize::zeroize(&mut asset_id_blinding);
        Zeroize::zeroize(&mut at);
        Zeroize::zeroize(&mut blindings_for_points);

        t_comm_r_i_amount.challenge_contribution(&mut transcript)?;

        for i in 0..num_asset_data_keys {
            re_randomized_points[i + 1].serialize_compressed(&mut transcript)?;
            t_points_r1[i].challenge_contribution(
                &r_1_protocol_base1[i],
                &blinding_base,
                &leg_enc.eph_pk_auds_meds[i].1.0,
                &mut transcript,
            )?;
            let base = &leg_enc.eph_pk_auds_meds[i].1.0;
            t_points_r2[i].challenge_contribution(
                base,
                &leg_enc.eph_pk_auds_meds[i].1.1,
                &mut transcript,
            )?;
            t_points_r3[i].challenge_contribution(
                base,
                &leg_enc.eph_pk_auds_meds[i].1.2,
                &mut transcript,
            )?;
            t_points_r4[i].challenge_contribution(
                base,
                &leg_enc.eph_pk_auds_meds[i].1.3,
                &mut transcript,
            )?;
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

        let challenge = transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        let mut wits = [
            comm_r_i_blinding,
            r_1,
            r_2,
            r_3,
            r_4,
            r_2_r_1_inv,
            r_3_r_1_inv,
            r_4_r_1_inv,
            amount,
        ];
        let resp_comm_r_i_amount = t_comm_r_i_amount.response(&wits, &challenge)?;

        Zeroize::zeroize(&mut wits);
        Zeroize::zeroize(&mut comm_r_i_blinding);
        Zeroize::zeroize(&mut r_1);
        Zeroize::zeroize(&mut r_2);
        Zeroize::zeroize(&mut r_3);
        Zeroize::zeroize(&mut r_4);
        Zeroize::zeroize(&mut r_2_r_1_inv);
        Zeroize::zeroize(&mut r_3_r_1_inv);
        Zeroize::zeroize(&mut r_4_r_1_inv);
        Zeroize::zeroize(&mut amount);

        let mut resp_eph_pk_auds_meds = Vec::with_capacity(asset_data.keys.len());

        for (((t_points_r1, t_points_r2), t_points_r3), t_points_r4) in t_points_r1
            .into_iter()
            .zip(t_points_r2.into_iter())
            .zip(t_points_r3.into_iter())
            .zip(t_points_r4.into_iter())
        {
            // Response for other witnesses will already be generated in sigma protocol for Bulletproof commitment
            let resp_1 = t_points_r1.gen_partial2_proof(&challenge);

            // TODO: Batch sigma can be used for these 3. And potentially these can be combined across keys. But then how to check the same response for r_2, r_3, r4?
            let resp_2 = t_points_r2.gen_partial_proof();

            let resp_3 = t_points_r3.gen_partial_proof();

            let resp_4 = t_points_r4.gen_partial_proof();
            resp_eph_pk_auds_meds.push(RespEphemeralPublicKey {
                r_1: resp_1,
                r_2: resp_2,
                r_3: resp_3,
                r_4: resp_4,
            });
        }

        // Response for witness will already be generated in sigma protocol for Bulletproof
        let resp_amount_enc = t_amount_enc.gen_partial_proof();

        let resp_asset_id = t_asset_id.gen_proof(&challenge);

        // Response for witnesses will already be generated in sigma protocol for above relation of asset_id and for Bulletproof
        let resp_asset_id_enc = t_asset_id_enc.gen_partial_proof();

        Ok(Self {
            r1cs_proof: None,
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
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G1>>,
            &mut RandomizedMultChecker<Affine<G0>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((_, rmc_0)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self.verify_and_return_tuples(
            leg_enc,
            tree_root,
            nonce,
            tree_parameters,
            asset_comm_params,
            enc_key_gen,
            enc_gen,
            rng,
            rmc_0,
        )?;

        match rmc {
            Some((rmc_1, rmc_0)) => {
                add_verification_tuples_to_rmc(even_tuple, odd_tuple, tree_parameters, rmc_1, rmc_0)
            }
            None => verify_given_verification_tuples(even_tuple, odd_tuple, tree_parameters),
        }
    }

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandParameters<G1, G0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G1>>, VerificationTuple<Affine<G0>>)> {
        let transcript_even = MerlinTranscript::new(SETTLE_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(SETTLE_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        self.verify_sigma_protocols_and_enforce_constraints(
            leg_enc,
            tree_root,
            nonce,
            tree_parameters,
            asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            rmc,
        )?;

        let r1cs_proof = self
            .r1cs_proof
            .as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof is missing".to_string()))?;
        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )
    }

    pub fn verify_sigma_protocols_and_enforce_constraints(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandParameters<G1, G0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        if asset_comm_params.comm_key.len() < self.re_randomized_points.len() {
            return Err(Error::InsufficientCommitmentKeyLength(
                asset_comm_params.comm_key.len(),
                self.re_randomized_points.len(),
            ));
        }
        if self.re_randomized_points.len() != self.resp_eph_pk_auds_meds.len() + 1 {
            return Err(Error::DifferentNumberOfRandomizedPointsAndResponses(
                self.re_randomized_points.len(),
                self.resp_eph_pk_auds_meds.len() + 1,
            ));
        }
        if self.resp_comm_r_i_amount.len() != 9 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                9,
                self.resp_comm_r_i_amount.len(),
            ));
        }

        // TODO: This is suboptimal if the same root is being used since the same children (of root) are being allocated each time this is called.
        let _ = self
            .re_randomized_path
            .select_and_rerandomize_verifier_gadget(
                tree_root,
                even_verifier,
                odd_verifier,
                &tree_parameters,
            );

        add_to_transcript!(
            odd_verifier.transcript(),
            ROOT_LABEL,
            tree_root,
            LEG_ENC_LABEL,
            leg_enc,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL,
            self.re_randomized_path
        );

        let rerandomized_leaf = self.re_randomized_path.get_rerandomized_leaf();

        verify_naive(
            even_verifier,
            rerandomized_leaf,
            self.re_randomized_points.clone(),
            &tree_parameters.odd_parameters,
        )?;

        let vars = odd_verifier.commit_vec(8, self.comm_r_i_amount);
        Self::enforce_constraints(odd_verifier, None, vars)?;

        let mut transcript = odd_verifier.transcript();

        self.t_comm_r_i_amount
            .serialize_compressed(&mut transcript)?;

        let aud_role_base = asset_comm_params.j_0.neg();
        let blinding_base = tree_parameters
            .odd_parameters
            .pc_gens
            .B_blinding
            .into_group()
            .neg()
            .into_affine();
        let mut r_1_protocol_base1 = Vec::with_capacity(self.resp_eph_pk_auds_meds.len());

        for i in 0..self.resp_eph_pk_auds_meds.len() {
            self.re_randomized_points[i + 1].serialize_compressed(&mut transcript)?;
            let role = leg_enc.eph_pk_auds_meds[i].0;
            let base1 = if role {
                (self.re_randomized_points[i + 1] + aud_role_base).into_affine()
            } else {
                self.re_randomized_points[i + 1]
            };
            self.resp_eph_pk_auds_meds[i].r_1.challenge_contribution(
                &base1,
                &blinding_base,
                &leg_enc.eph_pk_auds_meds[i].1.0,
                &mut transcript,
            )?;
            r_1_protocol_base1.push(base1);

            let base = &leg_enc.eph_pk_auds_meds[i].1.0;
            self.resp_eph_pk_auds_meds[i].r_2.challenge_contribution(
                base,
                &leg_enc.eph_pk_auds_meds[i].1.1,
                &mut transcript,
            )?;
            self.resp_eph_pk_auds_meds[i].r_3.challenge_contribution(
                base,
                &leg_enc.eph_pk_auds_meds[i].1.2,
                &mut transcript,
            )?;
            self.resp_eph_pk_auds_meds[i].r_4.challenge_contribution(
                base,
                &leg_enc.eph_pk_auds_meds[i].1.3,
                &mut transcript,
            )?;
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

        let challenge = transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        match rmc.as_mut() {
            Some(rmc) => {
                self.resp_amount_enc.verify_using_randomized_mult_checker(
                    leg_enc.ct_amount,
                    enc_key_gen,
                    enc_gen,
                    &challenge,
                    &self.resp_comm_r_i_amount.0[3],
                    &self.resp_comm_r_i_amount.0[8],
                    rmc,
                );

                self.resp_asset_id.verify_using_randomized_mult_checker(
                    self.re_randomized_points[0],
                    asset_comm_params.j_0,
                    tree_parameters.odd_parameters.pc_gens.B_blinding,
                    &challenge,
                    rmc,
                );

                self.resp_asset_id_enc.verify_using_randomized_mult_checker(
                    leg_enc.ct_asset_id,
                    enc_key_gen,
                    enc_gen,
                    &challenge,
                    &self.resp_comm_r_i_amount.0[4],
                    &self.resp_asset_id.response1,
                    rmc,
                );

                self.resp_comm_r_i_amount
                    .verify_using_randomized_mult_checker(
                        Self::bp_gens_vec(tree_parameters).to_vec(),
                        self.comm_r_i_amount,
                        self.t_comm_r_i_amount,
                        &challenge,
                        rmc,
                    )?;
            }
            None => {
                if !self.resp_amount_enc.verify(
                    &leg_enc.ct_amount,
                    &enc_key_gen,
                    &enc_gen,
                    &challenge,
                    &self.resp_comm_r_i_amount.0[3],
                    &self.resp_comm_r_i_amount.0[8],
                ) {
                    return Err(Error::ProofVerificationError(
                        "resp_amount_enc verification failed".into(),
                    ));
                }

                if !self.resp_asset_id.verify(
                    &self.re_randomized_points[0],
                    &asset_comm_params.j_0,
                    &tree_parameters.odd_parameters.pc_gens.B_blinding,
                    &challenge,
                ) {
                    return Err(Error::ProofVerificationError(
                        "resp_asset_id verification failed".into(),
                    ));
                }

                if !self.resp_asset_id_enc.verify(
                    &leg_enc.ct_asset_id,
                    &enc_key_gen,
                    &enc_gen,
                    &challenge,
                    &self.resp_comm_r_i_amount.0[4],
                    &self.resp_asset_id.response1,
                ) {
                    return Err(Error::ProofVerificationError(
                        "resp_asset_id_enc verification failed".into(),
                    ));
                }

                self.resp_comm_r_i_amount.is_valid(
                    &Self::bp_gens_vec(tree_parameters),
                    &self.comm_r_i_amount,
                    &self.t_comm_r_i_amount,
                    &challenge,
                )?;
            }
        }

        for i in 0..self.resp_eph_pk_auds_meds.len() {
            let resp = &self.resp_eph_pk_auds_meds[i];
            let D_r1 = &leg_enc.eph_pk_auds_meds[i].1.0;

            match rmc.as_mut() {
                Some(rmc) => {
                    resp.r_1.verify_using_randomized_mult_checker(
                        *D_r1,
                        r_1_protocol_base1[i],
                        blinding_base,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[1],
                        rmc,
                    );

                    resp.r_2.verify_using_randomized_mult_checker(
                        leg_enc.eph_pk_auds_meds[i].1.1,
                        *D_r1,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[5],
                        rmc,
                    );

                    resp.r_3.verify_using_randomized_mult_checker(
                        leg_enc.eph_pk_auds_meds[i].1.2,
                        *D_r1,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[6],
                        rmc,
                    );

                    resp.r_4.verify_using_randomized_mult_checker(
                        leg_enc.eph_pk_auds_meds[i].1.3,
                        *D_r1,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[7],
                        rmc,
                    );
                }
                None => {
                    if !resp.r_1.verify(
                        D_r1,
                        &r_1_protocol_base1[i],
                        &blinding_base,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[1],
                    ) {
                        return Err(Error::ProofVerificationError(format!(
                            "resp_leaf_points[{i}].r_1 verification mismatch"
                        )));
                    }

                    if !resp.r_2.verify(
                        &leg_enc.eph_pk_auds_meds[i].1.1,
                        D_r1,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[5],
                    ) {
                        return Err(Error::ProofVerificationError(format!(
                            "resp_leaf_points[{i}].r_2 verification mismatch"
                        )));
                    }

                    if !resp.r_3.verify(
                        &leg_enc.eph_pk_auds_meds[i].1.2,
                        D_r1,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[6],
                    ) {
                        return Err(Error::ProofVerificationError(format!(
                            "resp_leaf_points[{i}].r_3 verification mismatch"
                        )));
                    }

                    if !resp.r_4.verify(
                        &leg_enc.eph_pk_auds_meds[i].1.3,
                        D_r1,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[7],
                    ) {
                        return Err(Error::ProofVerificationError(format!(
                            "resp_leaf_points[{i}].r_4 verification mismatch"
                        )));
                    }
                }
            }
        }
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
        range_proof(cs, var_amount.into(), amount, BALANCE_BITS.into())?;
        Ok(())
    }

    pub(crate) fn bp_gens_vec(
        account_tree_params: &SelRerandParameters<G1, G0>,
    ) -> [Affine<G0>; 9] {
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
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        Self::new_with_given_transcript(
            rng,
            leg_enc,
            asset_id,
            mediator_sk,
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        asset_id: AssetId,
        mut mediator_sk: G::ScalarField,
        accept: bool,
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
        mut transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        ensure_correct_index(&leg_enc, index_in_asset_data)?;

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

        Zeroize::zeroize(&mut mediator_sk);

        enc_pk.challenge_contribution(&leg_enc.ct_asset_id, &minus_h, &D, &mut transcript)?;

        add_to_transcript!(
            transcript,
            LEG_ENC_LABEL,
            leg_enc,
            INDEX_IN_ASSET_DATA_LABEL,
            index_in_asset_data,
            NONCE_LABEL,
            nonce
        );

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
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        self.verify_with_given_transcript(
            leg_enc,
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
            rmc,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        leg_enc: LegEncryption<G>,
        accept: bool,
        index_in_asset_data: usize,
        nonce: &[u8],
        enc_gen: G,
        mut transcript: &mut MerlinTranscript,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        if index_in_asset_data >= leg_enc.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(index_in_asset_data));
        }
        // Role should be false for mediator
        if leg_enc.eph_pk_auds_meds[index_in_asset_data].0 {
            return Err(Error::MediatorNotFoundAtIndex(index_in_asset_data));
        }

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

        add_to_transcript!(
            transcript,
            LEG_ENC_LABEL,
            leg_enc,
            INDEX_IN_ASSET_DATA_LABEL,
            index_in_asset_data,
            NONCE_LABEL,
            nonce
        );

        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

        match rmc.as_mut() {
            Some(rmc) => {
                self.resp_enc_pk.verify_using_randomized_mult_checker(
                    D,
                    leg_enc.ct_asset_id,
                    minus_h,
                    &challenge,
                    rmc,
                );
            }
            None => {
                if !self
                    .resp_enc_pk
                    .verify(&D, &leg_enc.ct_asset_id, &minus_h, &challenge)
                {
                    return Err(Error::ProofVerificationError(
                        "resp_enc_pk verification failed".into(),
                    ));
                }
            }
        }

        Ok(())
    }
}

fn ensure_proper_leg_creation<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    leg: &Leg<Affine<G0>>,
    leg_enc: &LegEncryption<Affine<G0>>,
    asset_data: &AssetData<F0, F1, G0, G1>,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if leg.asset_id != asset_data.id {
            return Err(Error::IncompatibleAssetId(leg.asset_id, asset_data.id));
        }
        if leg.pk_auds_meds != asset_data.keys {
            return Err(Error::IncorrectKeyForAuditorsMediators);
        }
        if leg.pk_auds_meds.len() != leg_enc.eph_pk_auds_meds.len() {
            return Err(Error::IncompatibleLegAndLegEncryption(format!(
                "Number of public key in leg is {} and in leg encryption is {}",
                leg.pk_auds_meds.len(),
                leg_enc.eph_pk_auds_meds.len()
            )));
        }
        for i in 0..leg.pk_auds_meds.len() {
            if leg.pk_auds_meds[i].0 != leg_enc.eph_pk_auds_meds[i].0 {
                return Err(Error::IncompatibleLegAndLegEncryption(format!(
                    "Role of public key in leg is {} and in leg encryption is {}",
                    leg.pk_auds_meds[i].0, leg_enc.eph_pk_auds_meds[i].0
                )));
            }
        }
        Ok(())
    }
}

fn ensure_correct_index<G: AffineRepr>(
    leg_enc: &LegEncryption<G>,
    index_in_asset_data: usize,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if index_in_asset_data >= leg_enc.eph_pk_auds_meds.len() {
            return Err(Error::InvalidKeyIndex(index_in_asset_data));
        }
        // Role should be false for mediator
        if leg_enc.eph_pk_auds_meds[index_in_asset_data].0 {
            return Err(Error::MediatorNotFoundAtIndex(index_in_asset_data));
        }
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account::AccountCommitmentKeyTrait;
    use crate::account_registration::tests::setup_comm_key;
    use crate::keys::{DecKey, EncKey, SigKey, VerKey, keygen_enc, keygen_sig};
    use crate::util::{
        add_verification_tuples_batches_to_rmc, batch_verify_bp, get_verification_tuples_with_rng,
        prove_with_rng, verify_rmc, verify_with_rng,
    };
    use ark_ec::VariableBaseMSM;
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use bulletproofs::r1cs::{Prover, Verifier};
    use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
    use dock_crypto_utils::transcript::MerlinTranscript;
    use rand_core::CryptoRngCore;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type PallasFr = ark_pallas::Fr;
    type VestaFr = ark_vesta::Fr;

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
        let label = b"asset-tree-params";
        let asset_tree_params =
            SelRerandParameters::<VestaParameters, PallasParameters>::new_using_label(
                label,
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        // Called h in report
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 2;
        let num_mediators = 3;
        let asset_id = 1;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &asset_tree_params.even_parameters.bp_gens,
        );

        // Account signing (affirmation) keys
        let (_sk_s, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_sk_r, pk_r) = keygen_sig(&mut rng, sig_key_gen);

        // Encryption keys
        let (sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
        keys.extend(keys_auditor.iter().map(|(_, k)| (true, k.0)).into_iter());
        keys.extend(keys_mediator.iter().map(|(_, k)| (false, k.0)).into_iter());
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();

        // Check asset_data is correctly constructed
        let points = AssetData::points(asset_id, &asset_data.keys, &asset_comm_params);
        assert_eq!(points[0], asset_comm_params.j_0 * PallasFr::from(asset_id));
        for i in 0..num_auditors as usize {
            assert_eq!(
                points[i + 1].into_group(),
                asset_comm_params.j_0 + keys_auditor[i].1.0
            );
        }
        for i in 0..num_mediators as usize {
            assert_eq!(
                points[i + 1 + num_auditors as usize].into_group(),
                keys_mediator[i].1.0
            );
        }

        let x_coords = points
            .into_iter()
            .map(|p| (asset_tree_params.odd_parameters.delta + p).into_affine().x)
            .collect::<Vec<_>>();
        let expected_commitment = ark_vesta::Projective::msm(
            &asset_comm_params.comm_key[..(num_auditors + num_mediators + 1) as usize],
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

        let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Venue gets the leaf path from the tree
        let path = asset_tree.get_path_to_leaf_for_proof(0, 0);

        let root = asset_tree.root_node();

        let proof = SettlementTxnProof::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            path,
            asset_data.clone(),
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

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
                None,
            )
            .unwrap();

        let verifier_time_regular = clock.elapsed();

        let clock = Instant::now();
        let mut rmc_1 = RandomizedMultChecker::new(ark_vesta::Fr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
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
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();

        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let verifier_time_rmc = clock.elapsed();

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

        let (p1, p2, a, b) = leg_enc.decrypt_given_r(r, enc_key_gen, enc_gen).unwrap();
        assert_eq!(p1, pk_s.0);
        assert_eq!(p2, pk_r.0);
        assert_eq!(a, asset_id);
        assert_eq!(b, amount);

        let mut index = 0;
        for (d, _) in keys_auditor.into_iter().chain(keys_mediator.into_iter()) {
            let (p1, p2, a, b) = leg_enc.decrypt_given_key(&d.0, index, enc_gen).unwrap();
            assert_eq!(p1, pk_s.0);
            assert_eq!(p2, pk_r.0);
            assert_eq!(a, asset_id);
            assert_eq!(b, amount);
            index += 1;
        }

        println!("total proof size = {}", proof.compressed_size());
        println!("total prover time = {:?}", prover_time);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular, verifier_time_rmc
        );
    }

    #[test]
    fn mediator_action() {
        let mut rng = rand::thread_rng();

        // TODO: Generate by hashing public string
        let account_comm_key = setup_comm_key(b"testing");
        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);

        // Account signing (affirmation) keys
        let (_sk_s, pk_s) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (_sk_r, pk_r) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        // Encryption keys
        let (_sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

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

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let leg = Leg::new(
            pk_s.0,
            pk_r.0,
            keys.clone()
                .into_iter()
                .map(|(role, k, _)| (role, k))
                .collect(),
            amount,
            asset_id,
        )
        .unwrap();
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
        )
        .unwrap();
        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc.clone(),
                accept,
                mediator_index_in_keys,
                nonce,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time_regular = clock.elapsed();

        // Test verification with RMC as well
        let clock = Instant::now();
        let mut rmc = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
        proof
            .verify(
                leg_enc.clone(),
                accept,
                mediator_index_in_keys,
                nonce,
                enc_gen,
                Some(&mut rmc),
            )
            .unwrap();

        assert!(rmc.verify());
        let verifier_time_rmc = clock.elapsed();

        log::info!("proof size = {}", proof.compressed_size());
        log::info!("prover time = {:?}", prover_time);
        log::info!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular,
            verifier_time_rmc
        );

        match proof
            .verify(leg_enc.clone(), accept, 10, nonce, enc_gen, None)
            .err()
            .unwrap()
        {
            Error::InvalidKeyIndex(i) => assert_eq!(i, 10),
            _ => panic!("Didn't error but should have"),
        }

        match proof
            .verify(leg_enc.clone(), accept, 0, nonce, enc_gen, None)
            .err()
            .unwrap()
        {
            Error::MediatorNotFoundAtIndex(i) => assert_eq!(i, 0),
            _ => panic!("Didn't error but should have"),
        }
    }

    #[test]
    fn batch_leg_verification() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;

        // Create public params (generators, etc)
        let asset_tree_params = SelRerandParameters::<VestaParameters, PallasParameters>::new(
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

        let sig_key_gen = PallasA::rand(&mut rng);
        let enc_key_gen = PallasA::rand(&mut rng);

        let enc_gen = PallasA::rand(&mut rng);

        let num_auditors = 2;
        let num_mediators = 3;

        let batch_size = 5;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &asset_tree_params.even_parameters.bp_gens,
        );

        // Account signing (affirmation) keys
        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);

        // Encryption keys
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
        keys.extend(keys_auditor.iter().map(|(_, k)| (true, k.0)).into_iter());
        keys.extend(keys_mediator.iter().map(|(_, k)| (false, k.0)).into_iter());

        let mut asset_data_vec = Vec::with_capacity(batch_size);
        let mut commitments = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let asset_data = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.delta,
            )
            .unwrap();

            commitments.push(asset_data.commitment);
            asset_data_vec.push(asset_data);
        }

        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(2),
        );

        let amount = 100;
        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("batch_leg_nonce_{}", i).into_bytes())
            .collect();

        let mut legs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut leg_enc_rands = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);

        // Create legs for each asset
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
                .unwrap();

            let path = asset_tree.get_path_to_leaf_for_proof(i, 0);

            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
            paths.push(path);
        }

        let root = asset_tree.root_node();
        let mut proofs = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let proof = SettlementTxnProof::new(
                &mut rng,
                legs[i].clone(),
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                paths[i].clone(),
                asset_data_vec[i].clone(),
                &root,
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            proofs.push(proof);
        }

        let clock = Instant::now();

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            proofs[i]
                .verify(
                    &mut rng,
                    leg_encs[i].clone(),
                    &root,
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        // These can also be done in parallel
        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    leg_encs[i].clone(),
                    &root,
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        batch_verify_bp(even_tuples, odd_tuples, &asset_tree_params).unwrap();

        let batch_verifier_time = clock.elapsed();

        println!(
            "For {batch_size} leg verification proofs, verifier time = {:?}, batch verifier time {:?}",
            verifier_time, batch_verifier_time
        );

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    leg_encs[i].clone(),
                    &root,
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    Some(&mut rmc_1),
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        add_verification_tuples_batches_to_rmc(
            even_tuples,
            odd_tuples,
            &asset_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let batch_verifier_rmc_time = clock.elapsed();

        println!(
            "For {batch_size} leg verification proofs, batch_verifier_rmc_time time {:?}",
            batch_verifier_rmc_time
        );
    }

    #[test]
    fn combined_leg_verification() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 15; // increased for combined proofs
        const L: usize = 64;

        // Create public params (generators, etc)
        let asset_tree_params = SelRerandParameters::<VestaParameters, PallasParameters>::new(
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

        let sig_key_gen = PallasA::rand(&mut rng);
        let enc_key_gen = PallasA::rand(&mut rng);

        let enc_gen = PallasA::rand(&mut rng);

        let num_auditors = 2;
        let num_mediators = 3;

        let batch_size = 5;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &asset_tree_params.even_parameters.bp_gens,
        );

        // Account signing (affirmation) keys
        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);

        // Encryption keys
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
        keys.extend(keys_auditor.iter().map(|(_, k)| (true, k.0)).into_iter());
        keys.extend(keys_mediator.iter().map(|(_, k)| (false, k.0)).into_iter());

        let mut asset_data_vec = Vec::with_capacity(batch_size);
        let mut commitments = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let asset_data = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.delta,
            )
            .unwrap();

            commitments.push(asset_data.commitment);
            asset_data_vec.push(asset_data);
        }

        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(2),
        );

        let amount = 100;
        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("batch_leg_nonce_{}", i).into_bytes())
            .collect();

        let mut legs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut leg_enc_rands = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);

        // Create legs for each asset
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
                .unwrap();

            let path = asset_tree.get_path_to_leaf_for_proof(i, 0);

            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
            paths.push(path);
        }

        let root = asset_tree.root_node();

        let clock = Instant::now();
        let even_transcript = MerlinTranscript::new(SETTLE_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(SETTLE_TXN_ODD_LABEL);
        let mut even_prover =
            Prover::new(&asset_tree_params.even_parameters.pc_gens, even_transcript);
        let mut odd_prover = Prover::new(&asset_tree_params.odd_parameters.pc_gens, odd_transcript);

        let mut proofs = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let proof = SettlementTxnProof::new_with_given_prover(
                &mut rng,
                legs[i].clone(),
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                paths[i].clone(),
                asset_data_vec[i].clone(),
                &root,
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )
            .unwrap();
            proofs.push(proof);
        }

        let (even_bp, odd_bp) =
            prove_with_rng(even_prover, odd_prover, &asset_tree_params, &mut rng).unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(SETTLE_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(SETTLE_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        for i in 0..batch_size {
            proofs[i]
                .verify_sigma_protocols_and_enforce_constraints(
                    leg_encs[i].clone(),
                    &root,
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut even_verifier,
                    &mut odd_verifier,
                    None,
                )
                .unwrap();
        }

        verify_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            &asset_tree_params,
            &mut rng,
        )
        .unwrap();
        let verification_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(SETTLE_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(SETTLE_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            proofs[i]
                .verify_sigma_protocols_and_enforce_constraints(
                    leg_encs[i].clone(),
                    &root,
                    &nonces[i],
                    &asset_tree_params,
                    &asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    &mut even_verifier,
                    &mut odd_verifier,
                    Some(&mut rmc_1),
                )
                .unwrap();
        }

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &asset_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let rmc_verification_time = clock.elapsed();

        println!("Combined leg proving time = {:?}", proving_time);
        println!("Combined leg verification time = {:?}", verification_time);
        println!(
            "Combined leg RMC verification time = {:?}",
            rmc_verification_time
        );
        println!(
            "Combined proof size = {} bytes",
            even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
        );
    }

    // Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

    #[cfg(feature = "ignore_prover_input_sanitation")]
    mod input_sanitation_disabled {
        use super::*;

        #[test]
        fn settlement_proof_with_mismatched_asset_data() {
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 64;

            // Create public params (generators, etc)
            let asset_tree_params = SelRerandParameters::<VestaParameters, PallasParameters>::new(
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

            let sig_key_gen = PallasA::rand(&mut rng);
            let enc_key_gen = PallasA::rand(&mut rng);
            let enc_gen = PallasA::rand(&mut rng);

            let num_auditors = 2;
            let num_mediators = 3;
            let asset_id = 1;

            let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
                b"asset-comm-params",
                num_auditors + num_mediators,
                &asset_tree_params.even_parameters.bp_gens,
            );

            // Account signing (affirmation) keys
            let (_sk_s, pk_s) = keygen_sig(&mut rng, sig_key_gen);
            let (_sk_r, pk_r) = keygen_sig(&mut rng, sig_key_gen);

            // Encryption keys
            let (_sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
            let (_sk_r_e, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

            let keys_auditor = (0..num_auditors)
                .map(|_| keygen_enc(&mut rng, enc_key_gen))
                .collect::<Vec<_>>();
            let keys_mediator = (0..num_mediators)
                .map(|_| keygen_enc(&mut rng, enc_key_gen))
                .collect::<Vec<_>>();

            let mut keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
            keys.extend(keys_auditor.iter().map(|(_, k)| (true, k.0)).into_iter());
            keys.extend(keys_mediator.iter().map(|(_, k)| (false, k.0)).into_iter());

            // Create asset_data with one asset_id
            let asset_data = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.delta,
            )
            .unwrap();

            let set = vec![asset_data.commitment];
            let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
                &set,
                &asset_tree_params,
                Some(2),
            );

            let amount = 100;
            let nonce = b"test-nonce";

            // Create a leg with a different asset_id than the one in asset_data
            let different_asset_id = asset_id + 1;
            let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, different_asset_id).unwrap();
            let (leg_enc, leg_enc_rand) = leg
                .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
                .unwrap();

            let path = asset_tree.get_path_to_leaf_for_proof(0, 0);

            let root = asset_tree.root_node();

            let proof = SettlementTxnProof::new(
                &mut rng,
                leg.clone(),
                leg_enc.clone(),
                leg_enc_rand.clone(),
                path,
                asset_data.clone(),
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &root,
                        nonce,
                        &asset_tree_params,
                        &asset_comm_params,
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Create different keys for the leg
            let different_keys_auditor = (0..num_auditors)
                .map(|_| keygen_enc(&mut rng, enc_key_gen))
                .collect::<Vec<_>>();
            let different_keys_mediator = (0..num_mediators)
                .map(|_| keygen_enc(&mut rng, enc_key_gen))
                .collect::<Vec<_>>();

            let mut different_keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
            different_keys.extend(
                different_keys_auditor
                    .iter()
                    .map(|(_, k)| (true, k.0))
                    .into_iter(),
            );
            different_keys.extend(
                different_keys_mediator
                    .iter()
                    .map(|(_, k)| (false, k.0))
                    .into_iter(),
            );

            // Create a leg with different auditor/mediator keys than those in asset_data
            let leg_with_diff_keys =
                Leg::new(pk_s.0, pk_r.0, different_keys, amount, asset_id).unwrap();
            let (leg_enc, leg_enc_rand) = leg_with_diff_keys
                .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
                .unwrap();

            let path = asset_tree.get_path_to_leaf_for_proof(0, 0);

            let proof = SettlementTxnProof::new(
                &mut rng,
                leg_with_diff_keys.clone(),
                leg_enc.clone(),
                leg_enc_rand.clone(),
                path,
                asset_data.clone(),
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &root,
                        nonce,
                        &asset_tree_params,
                        &asset_comm_params,
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Create a leg with different role for one key than in leg_enc
            let mut keys_with_different_roles = keys.clone();
            // Change first key role from auditor (true) to mediator (false)
            keys_with_different_roles[0].0 = !keys_with_different_roles[0].0;

            let leg_with_diff_roles =
                Leg::new(pk_s.0, pk_r.0, keys_with_different_roles, amount, asset_id).unwrap();
            let (leg_enc, leg_enc_rand) = leg_with_diff_roles
                .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
                .unwrap();

            let path = asset_tree.get_path_to_leaf_for_proof(0, 0);

            let proof = SettlementTxnProof::new(
                &mut rng,
                leg_with_diff_roles.clone(),
                leg_enc.clone(),
                leg_enc_rand.clone(),
                path,
                asset_data.clone(),
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &root,
                        nonce,
                        &asset_tree_params,
                        &asset_comm_params,
                        enc_key_gen,
                        enc_gen,
                        None
                    )
                    .is_err()
            );
        }
    }
}
