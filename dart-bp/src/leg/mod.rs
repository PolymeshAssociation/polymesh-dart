pub mod leg_proof;
pub mod mediator;

pub mod public_asset_leg_proof;
pub mod settlement_proof;
#[cfg(test)]
pub mod tests;

pub use self::leg_proof::LegCreationProof;
pub use self::mediator::MediatorTxnProof;
use crate::discrete_log::solve_discrete_log_bsgs;
use crate::util::bp_gens_for_vec_commitment;
use crate::{Error, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::PrimeField;
use ark_pallas::PallasConfig;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use bulletproofs::BulletproofGens;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use core::iter;
use polymesh_dart_common::{AssetId, Balance, MAX_ASSET_ID, MAX_BALANCE};
use rand_core::CryptoRngCore;
use zeroize::{Zeroize, ZeroizeOnDrop};

pub use public_asset_leg_proof::PublicAssetLegCreationProof;
pub use settlement_proof::{LegProof, SettlementCreationProof};

pub const LEG_TXN_ODD_LABEL: &[u8; 17] = b"leg-txn-odd-level";
pub const LEG_TXN_EVEN_LABEL: &[u8; 18] = b"leg-txn-even-level";
pub const LEG_TXN_CHALLENGE_LABEL: &[u8; 17] = b"leg-txn-challenge";
pub const LEG_TXN_INSTANCE_LABEL: &[u8; 22] = b"leg-txn-extra-instance";

// Because of the way we organize keys, its better to have a single encryption key shared among all mediators. This is more efficient except when a mediator is removed which is rare

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AssetCommitmentParams<
    G0: SWCurveConfig + Clone + Copy,
    G1: SWCurveConfig<ScalarField = G0::BaseField, BaseField = G0::ScalarField> + Clone + Copy,
> {
    pub j_0: Affine<G0>,
    pub j_1: Affine<G0>,
    pub comm_key: Vec<Affine<G1>>,
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
        let j_1 = hash_to_pallas(label, b" : j_1").into_affine();
        let comm_key = bp_gens_for_vec_commitment(num_keys + 1, leaf_layer_bp_gens).collect();
        Self { j_0, j_1, comm_key }
    }
}

/// AssetData cannot have zero encryption keys but non-zero mediator keys
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
    /// Encryption keys shared between auditors and mediators
    pub enc_keys: Vec<Affine<G0>>,
    /// Affirmation keys of mediators. These are not shared and each mediator has access to one of the encryption keys.
    /// (index in enc_keys, affirmation-key)
    pub med_keys: Vec<(u8, Affine<G0>)>,
    /// A non-hiding commitment to asset-id and keys. Created by taking x-coordinates of the points returned by [`AssetData::points`] and
    /// committing to them in a non-hiding Pedersen commitment, using the same commitment key as used in BP.
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
        enc_keys: Vec<Affine<G0>>,
        med_keys: Vec<(u8, Affine<G0>)>,
        params: &AssetCommitmentParams<G0, G1>,
        delta: Affine<G0>,
    ) -> Result<Self> {
        let total_keys = enc_keys.len() + med_keys.len();
        if params.comm_key.len() < total_keys + 1 {
            return Err(Error::InsufficientCommitmentKeyLength(
                params.comm_key.len(),
                total_keys + 1,
            ));
        }
        for (idx, _) in &med_keys {
            if *idx as usize >= enc_keys.len() {
                return Err(Error::InvalidKeyIndex(*idx as usize));
            }
        }

        // Asset id could be kept out of `points` and committed in commitment directly using one of the generators of comm_key
        // but that pushes asset id into the other group which makes the leg creation txn proof quite expensive
        let points = Self::points(id, &enc_keys, &med_keys, params);
        let x_coords = points
            .into_iter()
            .map(|p| (delta + p).into_affine().x)
            .collect::<Vec<_>>();
        let commitment =
            G1::msm(&params.comm_key[..(total_keys + 1)], x_coords.as_slice()).unwrap();
        Ok(Self {
            id,
            enc_keys,
            med_keys,
            commitment: commitment.into_affine(),
        })
    }

    /// Return 1 point per key and role combined. The idea is to have 1 point per auditor/mediator and the
    /// point should encapsulate all info about that auditor/mediator
    /// Points are as list `[<asset_id * j_0, j_0 * role + en_1, j_0 * role + en_2, ..., j_0 * role + en_n, j_0 * role + j_1 * med_1_en + med_1, j_0 * role + j_1 * med_2_en + med_2, ..., j_0 * role + j_1 * med_m_en + med_m>]`
    /// where `en_i` are the encryption keys, `med_i` are the mediator affirmation keys, `role = 0` for encryption keys
    /// and `role = 1` for mediator keys and `med_i_en` refers to the index of encryption key help by `i`-th mediator. This index is
    /// in the list of encryption keys `en_i`
    pub fn points(
        asset_id: AssetId,
        enc_keys: &[Affine<G0>],
        med_keys: &[(u8, Affine<G0>)],
        params: &AssetCommitmentParams<G0, G1>,
    ) -> Vec<Affine<G0>> {
        iter::once((params.j_0 * G0::ScalarField::from(asset_id)).into_affine())
            // For encryption keys, role = 0 and thus point is just the key itself
            .chain(enc_keys.into_iter().map(|k| *k))
            // For mediator keys, role = 1 and thus point is the key + j_0 + j_1 * index where index corresponds to the encryption key of this mediator
            .chain(med_keys.into_iter().map(|(i, k)| {
                (params.j_0 + params.j_1 * G0::ScalarField::from(*i) + *k).into_affine()
            }))
            .collect()
    }

    pub fn num_encryption_keys(&self) -> usize {
        self.enc_keys.len()
    }

    pub fn num_mediator_keys(&self) -> usize {
        self.med_keys.len()
    }

    pub fn num_total_keys(&self) -> usize {
        self.enc_keys.len() + self.med_keys.len()
    }

    // More efficient update methods can be added in future
}

#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct LegCore<G: AffineRepr> {
    /// Encryption public key of sender
    pub pk_s: G,
    /// Encryption public key of receiver
    pub pk_r: G,
    pub amount: Balance,
    pub asset_id: AssetId,
}

#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct Leg<G: AffineRepr> {
    pub core: LegCore<G>,
    /// Encryption keys for which `LegCore` will be encrypted.
    /// These keys are whats stored along the asset-id in [`AssetData`] and are hidden from verifier unless explicitly revealed
    pub enc_keys: Vec<G>,
    /// Mediator affirmation keys
    /// List of pairs of the form `(enc-key-index, mediator-affirmation-key)` where `enc-key-index` is the index
    /// of key in `enc_keys` used when encrypting `mediator-affirmation-key`
    /// These keys are whats stored along the asset-id in [`AssetData`] and are hidden from verifier unless explicitly revealed
    /// A leg cannot have zero encryption keys but non-zero mediator affirmation keys.
    pub med_keys: Vec<(u8, G)>,
    /// Encryption keys for which [`LegCore`] will be encrypted.
    /// These keys are not stored along the asset-id in [`AssetData`] but provided by the leg creator and are always revealed to the verifier
    pub public_enc_keys: Vec<G>,
}

#[derive(Clone)]
pub struct LegEncConfig {
    /// If `parties_see_each_other` is true, sender can decrypt receiver's pk and vice versa.
    pub parties_see_each_other: bool,
    /// If `true`, asset-id is revealed in the leg else a curve-tree membership proof in the asset
    /// tree is created
    pub reveal_asset_id: bool,
}

impl Default for LegEncConfig {
    /// By default, both parties see each other and the asset-id is hidden.
    fn default() -> Self {
        Self {
            parties_see_each_other: true,
            reveal_asset_id: false,
        }
    }
}

/// Twisted Elgamal's ephemeral public key per auditor/mediator `(pk * r_1, pk * r_2, pk * r_3, Option<pk * r_4>)`
/// The last component is `None` when asset-id is revealed.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EphemeralPublicKey<G: AffineRepr>(pub G, pub G, pub G, pub Option<G>);

/// Sender's ephemeral public keys. Index 1 is None when the sender cannot decrypt the receiver's pk.
/// Index 3 is None when asset-id is revealed (not encrypted).
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderEphemeralPublicKey<G: AffineRepr>(pub G, pub Option<G>, pub G, pub Option<G>);

/// Receiver's ephemeral public keys. Index 0 is None when the receiver cannot decrypt the sender's pk.
/// Index 3 is None when asset-id is revealed (not encrypted).
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiverEphemeralPublicKey<G: AffineRepr>(pub Option<G>, pub G, pub G, pub Option<G>);

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
            Self::Sender(s) => s.2,
            Self::Receiver(r) => r.2,
        }
    }

    /// Ephemeral key for asset_id encryption (index 3) — `None` when asset ID is revealed
    pub fn eph_pk_asset_id(&self) -> Option<G> {
        match self {
            Self::Sender(s) => s.3,
            Self::Receiver(r) => r.3,
        }
    }

    /// Ephemeral key identifying the party (index 0 for sender, index 1 for receiver)
    pub fn eph_pk_participant(&self) -> G {
        match self {
            Self::Sender(s) => s.0,
            Self::Receiver(r) => r.1,
        }
    }
}

/// (r_1, r_2, r_3, r_4) — r_4 is `None` when asset-id is revealed
#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct LegEncryptionRandomness<F: PrimeField> {
    pub r1: F,
    pub r2: F,
    pub r3: F,
    pub r4: Option<F>,
    /// Randomness used for creating ephemeral public keys for encryption keys corresponding to mediators.
    pub r_meds: Vec<F>,
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionCore<G: AffineRepr> {
    pub ct_s: G,
    pub ct_r: G,
    pub ct_amount: G,
    /// `None` when asset-id is revealed (not encrypted); `Some(ct)` when encrypted
    pub ct_asset_id: Option<G>,
}

impl<G: AffineRepr> LegEncryptionCore<G> {
    /// Returns the ciphertext for the participant, `ct_s` for sender, `ct_r` for receiver
    pub fn ct_participant(&self, is_sender: bool) -> G {
        if is_sender { self.ct_s } else { self.ct_r }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorEncryptions<G: AffineRepr> {
    /// Ephemeral encryption public keys for mediators in the order they appear in `ct_meds`.
    /// The index corresponds to the encryption key from [`AssetData`].
    ///
    /// Invariant: `ct_meds.len() == eph_pk_med_keys.len()`.
    pub eph_pk_med_keys: Vec<(u8, G)>,
    /// Encryption of mediator affirmation keys in the order they appear in [`AssetData`].
    /// These only need to be decrypted by the corresponding mediator and none other.
    pub ct_meds: Vec<G>,
}

/// Twisted Elgamal encryption of sender pk, receiver pk, amount and asset id
// TODO: Capture core, eph_pk_s, eph_pk_r into a struct that can be passed to sender/receiver affirmations
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryption<G: AffineRepr> {
    pub core: LegEncryptionCore<G>,
    pub eph_pk_s: SenderEphemeralPublicKey<G>,
    pub eph_pk_r: ReceiverEphemeralPublicKey<G>,
    /// Ephemeral public keys of auditors in the order they appear in [`AssetData`].
    pub eph_pk_enc_keys: Vec<EphemeralPublicKey<G>>,
    /// Ephemeral public keys of auditors in the order they were passed by leg creator.
    pub eph_pk_public_enc_keys: Vec<EphemeralPublicKey<G>>,
    pub mediators: MediatorEncryptions<G>,
}

impl<F: PrimeField, G: AffineRepr<ScalarField = F>> Leg<G> {
    /// Its assumed that caller ensures that no duplicate keys are passed for
    /// auditors and mediators else the proofs will be more expensive than they need to be.
    /// Also assumes that all keys are passed and in the same order as in [`AssetData`]
    /// `pk_s_e` and `pk_r_e` are encryption keys of sender and receiver
    /// `enc_keys` are the encryption keys with which the leg details are encrypted and these shared among
    /// auditors and mediators and should be in the order they appear in [`AssetData`]
    pub fn new(
        pk_s_e: G,
        pk_r_e: G,
        amount: Balance,
        asset_id: AssetId,
        enc_keys: Vec<G>,
        med_keys: Vec<(u8, G)>,
        public_enc_keys: Vec<G>,
    ) -> Result<Self> {
        if amount > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount));
        }
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }
        for (idx, _) in &med_keys {
            if *idx as usize >= enc_keys.len() {
                return Err(Error::InvalidKeyIndex(*idx as usize));
            }
        }
        Ok(Self {
            core: LegCore {
                pk_s: pk_s_e,
                pk_r: pk_r_e,
                amount,
                asset_id,
            },
            enc_keys,
            med_keys,
            public_enc_keys,
        })
    }

    pub fn encrypt<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        config: LegEncConfig,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<(LegEncryption<G>, LegEncryptionRandomness<F>)> {
        let r1 = F::rand(rng);
        let r2 = F::rand(rng);
        let r3 = F::rand(rng);
        let r4 = (!config.reveal_asset_id).then(|| F::rand(rng));

        let mut amount = F::from(self.core.amount);
        let mut asset_id = F::from(self.core.asset_id);

        // Optimz: Lot of the following operations can benefit from `WindowTable`

        let pk_s_enc = self.core.pk_s;
        let pk_r_enc = self.core.pk_r;

        let ct_s = (enc_key_gen * r1 + pk_s_enc).into_affine();
        let ct_r = (enc_key_gen * r2 + pk_r_enc).into_affine();
        let ct_amount = (enc_key_gen * r3 + enc_gen * amount).into_affine();

        // Encrypt asset-id if it isn't revealed
        let ct_asset_id = if config.reveal_asset_id {
            None
        } else {
            Some((enc_key_gen * r4.unwrap() + enc_gen * asset_id).into_affine())
        };

        // If parties are allowed to see each other create ephemeral public keys for those parts else skip
        let cross_pk = if config.parties_see_each_other {
            (
                Some((pk_s_enc * r2).into_affine()),
                Some((pk_r_enc * r1).into_affine()),
            )
        } else {
            (None, None)
        };

        let eph_pk_s = SenderEphemeralPublicKey::<G>(
            (pk_s_enc * r1).into_affine(),
            cross_pk.0,
            (pk_s_enc * r3).into_affine(),
            r4.map(|r| (pk_s_enc * r).into_affine()),
        );

        let eph_pk_r = ReceiverEphemeralPublicKey::<G>(
            cross_pk.1,
            (pk_r_enc * r2).into_affine(),
            (pk_r_enc * r3).into_affine(),
            r4.map(|r| (pk_r_enc * r).into_affine()),
        );

        let enc_keys = self.enc_keys.iter().map(|pk| {
            EphemeralPublicKey::<G>(
                (*pk * r1).into_affine(),
                (*pk * r2).into_affine(),
                (*pk * r3).into_affine(),
                r4.map(|r| (*pk * r).into_affine()),
            )
        });

        let public_enc_keys = self.public_enc_keys.iter().map(|pk| {
            EphemeralPublicKey::<G>(
                (*pk * r1).into_affine(),
                (*pk * r2).into_affine(),
                (*pk * r3).into_affine(),
                r4.map(|r| (*pk * r).into_affine()),
            )
        });

        let mut r_meds = Vec::with_capacity(self.med_keys.len());
        let mut ct_meds = Vec::with_capacity(self.med_keys.len());
        let mut eph_pk_med_keys = Vec::with_capacity(self.med_keys.len());

        for i in 0..self.med_keys.len() {
            let r = F::rand(rng);
            ct_meds.push(enc_key_gen * r + self.med_keys[i].1);
            eph_pk_med_keys.push((
                self.med_keys[i].0,
                (self.enc_keys[self.med_keys[i].0 as usize] * r).into_affine(),
            ));
            r_meds.push(r);
        }

        Zeroize::zeroize(&mut amount);
        Zeroize::zeroize(&mut asset_id);

        Ok((
            LegEncryption {
                core: LegEncryptionCore {
                    ct_s,
                    ct_r,
                    ct_amount,
                    ct_asset_id,
                },
                eph_pk_s,
                eph_pk_r,
                eph_pk_enc_keys: enc_keys.collect(),
                eph_pk_public_enc_keys: public_enc_keys.collect(),
                mediators: MediatorEncryptions {
                    ct_meds: G::Group::normalize_batch(&ct_meds),
                    eph_pk_med_keys,
                },
            },
            LegEncryptionRandomness {
                r1,
                r2,
                r3,
                r4,
                r_meds,
            },
        ))
    }
}

impl<F: PrimeField, G: AffineRepr<ScalarField = F>> LegEncryption<G> {
    pub fn is_asset_id_revealed(&self) -> bool {
        self.core.ct_asset_id.is_none()
    }

    /// Returns true if senders and receivers are allowed to see each other. Here the leg encryption
    /// contains required elements
    pub fn do_parties_see_each_other(&self) -> bool {
        self.eph_pk_s.1.is_some() & self.eph_pk_r.0.is_some()
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id_ciphertext(&self) -> Option<G> {
        self.core.ct_asset_id
    }

    pub fn ct_s(&self) -> G {
        self.core.ct_s
    }

    pub fn ct_r(&self) -> G {
        self.core.ct_r
    }

    pub fn ct_amount(&self) -> G {
        self.core.ct_amount
    }

    /// Returns the ciphertext for the participant, `ct_s` for sender, `ct_r` for receiver
    pub fn ct_participant(&self, is_sender: bool) -> G {
        self.core.ct_participant(is_sender)
    }

    pub fn num_mediators(&self) -> usize {
        self.mediators.ct_meds.len()
    }

    pub fn eph_pk_participant(&self, is_sender: bool) -> G {
        if is_sender {
            self.eph_pk_s.0
        } else {
            self.eph_pk_r.1
        }
    }

    pub fn eph_pk_and_ct_participant(&self, is_sender: bool) -> (G, G) {
        if is_sender {
            (self.eph_pk_s.0, self.core.ct_s)
        } else {
            (self.eph_pk_r.1, self.core.ct_r)
        }
    }

    pub fn eph_pk_asset_id(&self, is_sender: bool) -> Option<G> {
        if is_sender {
            self.eph_pk_s.3
        } else {
            self.eph_pk_r.3
        }
    }

    pub fn eph_pk_amount(&self, is_sender: bool) -> G {
        if is_sender {
            self.eph_pk_s.2
        } else {
            self.eph_pk_r.2
        }
    }

    /// Decrypt a single ciphertext element using `sk_enc_inv` and the corresponding ephemeral key.
    /// `plaintext = ct - eph_pk * sk_enc_inv`
    pub fn decrypt_element_with_sk_inv(sk_inv: &F, ct: G, eph_pk: G) -> G::Group {
        ct.into_group() - eph_pk * sk_inv
    }

    /// Decrypt as sender using `sk_enc`. Sender can always decrypt own pk, amount, and asset_id
    /// when it was encrypted; returns `None` for asset_id if it was not encrypted (revealed).
    /// Receiver pk is only decryptable when `eph_pk_s.1` is present.
    pub fn decrypt_as_sender(
        &self,
        sk_enc: &F,
        enc_gen: G,
    ) -> Result<(G, Option<G>, Option<AssetId>, Balance)> {
        self.decrypt_as_sender_with_limits(sk_enc, enc_gen, None, None)
    }

    pub fn decrypt_as_sender_with_limits(
        &self,
        sk_enc: &F,
        enc_gen: G,
        max_asset_id: Option<AssetId>,
        max_amount: Option<Balance>,
    ) -> Result<(G, Option<G>, Option<AssetId>, Balance)> {
        let enc_gen = enc_gen.into_group();
        let max_asset_id = max_asset_id.unwrap_or(MAX_ASSET_ID);
        let max_amount = max_amount.unwrap_or(MAX_BALANCE);

        let sk_enc_inv = sk_enc
            .inverse()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;

        let asset_id =
            self.decrypt_asset_id_as_participant(true, &sk_enc_inv, enc_gen, max_asset_id)?;

        let amount_pt =
            Self::decrypt_element_with_sk_inv(&sk_enc_inv, self.core.ct_amount, self.eph_pk_s.2);
        let amount = solve_discrete_log_bsgs::<G::Group>(max_amount, enc_gen, amount_pt)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))?;

        let sender =
            Self::decrypt_element_with_sk_inv(&sk_enc_inv, self.core.ct_s, self.eph_pk_s.0)
                .into_affine();
        let receiver = self.eph_pk_s.1.map(|eph| {
            Self::decrypt_element_with_sk_inv(&sk_enc_inv, self.core.ct_r, eph).into_affine()
        });

        Ok((sender, receiver, asset_id, amount))
    }

    /// Decrypt as receiver using `sk_enc`. Receiver can always decrypt own pk, amount, and asset_id
    /// when it was encrypted; returns `None` for asset_id if it was not encrypted (revealed).
    /// Sender pk is only decryptable when `eph_pk_r.0` is present.
    pub fn decrypt_as_receiver(
        &self,
        sk_enc: &F,
        enc_gen: G,
    ) -> Result<(Option<G>, G, Option<AssetId>, Balance)> {
        self.decrypt_as_receiver_with_limits(sk_enc, enc_gen, None, None)
    }

    pub fn decrypt_as_receiver_with_limits(
        &self,
        sk_enc: &F,
        enc_gen: G,
        max_asset_id: Option<AssetId>,
        max_amount: Option<Balance>,
    ) -> Result<(Option<G>, G, Option<AssetId>, Balance)> {
        let enc_gen = enc_gen.into_group();
        let max_asset_id = max_asset_id.unwrap_or(MAX_ASSET_ID);
        let max_amount = max_amount.unwrap_or(MAX_BALANCE);

        let sk_enc_inv = sk_enc
            .inverse()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;

        let asset_id =
            self.decrypt_asset_id_as_participant(false, &sk_enc_inv, enc_gen, max_asset_id)?;

        let amount_pt =
            Self::decrypt_element_with_sk_inv(&sk_enc_inv, self.core.ct_amount, self.eph_pk_r.2);
        let amount = solve_discrete_log_bsgs::<G::Group>(max_amount, enc_gen, amount_pt)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))?;

        let receiver =
            Self::decrypt_element_with_sk_inv(&sk_enc_inv, self.core.ct_r, self.eph_pk_r.1)
                .into_affine();
        let sender = self.eph_pk_r.0.map(|eph| {
            Self::decrypt_element_with_sk_inv(&sk_enc_inv, self.core.ct_s, eph).into_affine()
        });

        Ok((sender, receiver, asset_id, amount))
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given decryption key of auditor/mediator.
    /// `key_index` is the index of auditor/mediator key in [`AssetData`]
    pub fn decrypt_given_key(
        &self,
        sk: &F,
        is_public_enc_key: bool,
        key_index: usize,
        enc_gen: G,
    ) -> Result<(G, G, Option<AssetId>, Balance)> {
        self.decrypt_given_key_with_limits(sk, is_public_enc_key, key_index, enc_gen, None, None)
    }

    /// Return (sender-pk, receiver-pk, asset-id, amount) in the leg given decryption key of auditor/mediator.
    /// `key_index` is the index of auditor/mediator key in [`AssetData`]
    pub fn decrypt_given_key_with_limits(
        &self,
        sk: &F,
        is_public_enc_key: bool,
        key_index: usize,
        enc_gen: G,
        max_asset_id: Option<AssetId>,
        max_amount: Option<Balance>,
    ) -> Result<(G, G, Option<AssetId>, Balance)> {
        let eph_keys = if is_public_enc_key {
            &self.eph_pk_public_enc_keys
        } else {
            &self.eph_pk_enc_keys
        };
        if key_index >= eph_keys.len() {
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
        let asset_id =
            self.decrypt_asset_id(&sk_inv, is_public_enc_key, key_index, enc_gen, max_asset_id)?;
        let amount =
            self.decrypt_amount(&sk_inv, is_public_enc_key, key_index, enc_gen, max_amount)?;

        let sender = Self::decrypt_as_group_element(&sk_inv, self.core.ct_s, eph_keys[key_index].0);
        let receiver =
            Self::decrypt_as_group_element(&sk_inv, self.core.ct_r, eph_keys[key_index].1);

        Zeroize::zeroize(&mut sk_inv);

        Ok((
            sender.into_affine(),
            receiver.into_affine(),
            asset_id.map(|a| a as AssetId),
            amount,
        ))
    }

    pub fn decrypt_asset_id(
        &self,
        sk_inv: &F,
        is_public: bool,
        key_index: usize,
        enc_gen: G::Group,
        max_asset_id: AssetId,
    ) -> Result<Option<u64>> {
        let eph_keys = if is_public {
            &self.eph_pk_public_enc_keys
        } else {
            &self.eph_pk_enc_keys
        };
        if key_index >= eph_keys.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }

        self.core
            .ct_asset_id
            .map(|ct| {
                let asset_id =
                    Self::decrypt_as_group_element(sk_inv, ct, eph_keys[key_index].3.unwrap());
                solve_discrete_log_bsgs::<G::Group>(max_asset_id as _, enc_gen, asset_id)
                    .ok_or_else(|| {
                        Error::DecryptionFailed("Discrete log of `asset_id` failed.".into())
                    })
            })
            .transpose()
    }

    pub fn decrypt_amount(
        &self,
        sk_inv: &F,
        is_public: bool,
        key_index: usize,
        enc_gen: G::Group,
        max_amount: Balance,
    ) -> Result<u64> {
        let eph_keys = if is_public {
            &self.eph_pk_public_enc_keys
        } else {
            &self.eph_pk_enc_keys
        };
        if key_index >= eph_keys.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }
        let amount =
            Self::decrypt_as_group_element(sk_inv, self.core.ct_amount, eph_keys[key_index].2);

        solve_discrete_log_bsgs::<G::Group>(max_amount, enc_gen, amount)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))
    }

    pub fn decrypt_as_group_element(sk_inv: &F, encrypted: G, eph_pk: G) -> G::Group {
        encrypted.into_group() - eph_pk * sk_inv
    }

    fn decrypt_asset_id_as_participant(
        &self,
        is_sender: bool,
        sk_enc_inv: &F,
        enc_gen: G::Group,
        max_asset_id: AssetId,
    ) -> Result<Option<AssetId>> {
        let eph_pk = self.eph_pk_asset_id(is_sender);
        self.core
            .ct_asset_id
            .map(|ct| {
                let eph_pk_asset_id = eph_pk.ok_or_else(|| {
                    Error::DecryptionFailed("Missing ephemeral key for asset ID decryption".into())
                })?;
                let asset_id_pt =
                    Self::decrypt_element_with_sk_inv(&sk_enc_inv, ct, eph_pk_asset_id);
                solve_discrete_log_bsgs::<G::Group>(max_asset_id as u64, enc_gen, asset_id_pt)
                    .ok_or_else(|| {
                        Error::DecryptionFailed("Discrete log of `asset_id` failed.".into())
                    })
                    .map(|id| id as AssetId)
            })
            .transpose()
    }
}

#[derive(Copy, Clone, Debug)]
pub struct AmountCiphertext<G: AffineRepr>(
    /// ct_amount
    pub G,
    /// eph_pk_amount
    pub G,
);

mod serialization {
    use super::*;
    use ark_serialize::{Compress, SerializationError, Valid, Validate};
    use ark_std::io::{Read, Write};

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
