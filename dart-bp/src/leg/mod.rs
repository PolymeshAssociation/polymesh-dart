pub mod leg_proof;
pub mod mediator;

pub mod public_asset_leg_proof;
pub mod settlement_proof;
/// PoC: chunked settlement proof for evaluating the verifier-first chunking optimization.
#[cfg(feature = "std")]
pub mod settlement_proof_chunked;
#[cfg(test)]
pub mod tests;

pub use self::leg_proof::LegCreationProof;
pub use self::mediator::{MediatorTxnOldProof, MediatorTxnProof};
use crate::discrete_log::solve_discrete_log_bsgs;
use crate::util::bp_gens_for_vec_commitment;
use crate::{Error, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::PrimeField;
use ark_pallas::PallasConfig;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{string::ToString, vec::Vec};
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

// Because of the way we organize keys, its better to have a single encryption key shared among all mediators.
// This is more efficient except when a mediator is removed which is rare. Also better for asset-id
// privacy since an uncommon indexing will reveal the asset during proof

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AssetCommitmentParams<
    G0: SWCurveConfig + Clone + Copy,
    G1: SWCurveConfig<ScalarField = G0::BaseField, BaseField = G0::ScalarField> + Clone + Copy,
> {
    pub j_0: Affine<G0>,
    /// Generators for the leaf commitment. The first `2 * (1 + num_enc_keys + num_med_keys)`
    /// generators commit both coordinates of the asset-id point, the auditor encryption keys and the
    /// mediator affirmation keys (the "point block"), 2 generators per point. One trailing generator
    /// at index `2 * (1 + num_enc_keys + num_med_keys)` commits the mediator count.
    pub comm_key: Vec<Affine<G1>>,
    /// Maximum number of (auditor/mediator shared) encryption keys these params are sized for.
    pub num_enc_keys: u32,
    /// Maximum number of mediator keys these params are sized for.
    pub num_med_keys: u32,
}

impl<
    G0: SWCurveConfig + Clone + Copy,
    G1: SWCurveConfig<ScalarField = G0::BaseField, BaseField = G0::ScalarField> + Clone + Copy,
> AssetCommitmentParams<G0, G1>
{
    /// Index of the generator committing the mediator count.
    pub fn count_gen(&self) -> Affine<G1> {
        self.comm_key[2 * (1 + self.num_enc_keys as usize + self.num_med_keys as usize)]
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
    /// Need the same generators as used in Bulletproofs of the curve tree system because the verifier "commits" to the x-coordinates using the same key.
    /// `num_enc_keys` and `num_med_keys` are the maximum auditor/mediator counts the params are sized for.
    pub fn new(
        label: &[u8],
        num_enc_keys: u32,
        num_med_keys: u32,
        leaf_layer_bp_gens: &BulletproofGens<Affine<G1>>,
    ) -> Self {
        let j_0 = hash_to_pallas(label, b" : j_0").into_affine();
        // For committing (x,y) coords of asset-id point and enc and mediator keys and one for count
        let comm_key = bp_gens_for_vec_commitment(
            2 * (1 + num_enc_keys + num_med_keys) + 1,
            leaf_layer_bp_gens,
        )
        .collect();
        Self {
            j_0,
            comm_key,
            num_enc_keys,
            num_med_keys,
        }
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
    pub med_keys: Vec<Affine<G0>>,
    /// A non-hiding commitment to asset-id and keys. Created by taking both coordinates of the points returned by [`AssetData::points`] and
    /// committing to them in a non-hiding Pedersen commitment, using the same commitment key as used in BP.
    pub commitment: Affine<G1>,
}

#[cfg_attr(
    all(test, feature = "nightly_mocking_tests"),
    mocktopus::macros::mockable
)]
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
        med_keys: Vec<Affine<G0>>,
        params: &AssetCommitmentParams<G0, G1>,
    ) -> Result<Self> {
        let n = enc_keys.len();
        let m = med_keys.len();
        if n > params.num_enc_keys as usize || m > params.num_med_keys as usize {
            return Err(Error::InsufficientCommitmentKeyLength(
                params.comm_key.len(),
                2 * (1 + params.num_enc_keys as usize + params.num_med_keys as usize) + 1,
            ));
        }
        // Asset id could be kept out of `points` and committed in commitment directly using one of the generators of comm_key
        // but that pushes asset id into the other group which makes the leg creation txn proof quite expensive.
        // Point block: both coordinates of [asset_id, auditor pks, mediator pks] under
        // comm_key[0 .. 2*(1+n+m)], 2 generators per point. Committing both coordinates pins each
        // point (committing only the x-coordinate would leave the y-sign free).
        let points = Self::_points(id, &enc_keys, &med_keys, params);
        let num_points = points.len();
        let mut gens = params.comm_key[..2 * num_points].to_vec();
        let mut scalars = Vec::with_capacity(2 * num_points + 1);
        for p in &points {
            let (x, y) = p.xy().ok_or(Error::PointAtIdentity)?;
            scalars.push(x);
            scalars.push(y);
        }
        // Mediator count under the trailing generator.
        gens.push(params.count_gen());
        scalars.push(F1::from(m as u64));
        let commitment = G1::msm(&gens, scalars.as_slice()).unwrap();
        Ok(Self {
            id,
            enc_keys,
            med_keys,
            commitment: commitment.into_affine(),
        })
    }

    pub fn points(&self, params: &AssetCommitmentParams<G0, G1>) -> Vec<Affine<G0>> {
        Self::_points(self.id, &self.enc_keys, &self.med_keys, params)
    }

    /// Points `[(asset_id + 1) * j_0, en_1, ..., en_n, med_1, ..., med_m]`, mediator keys as bare
    /// points. The asset-id scalar is offset by 1 so the asset-id point is never the identity (which
    /// the leaf commitment rejects) even for `asset_id == 0`. The point relation in the leg proof
    /// subtracts `j_0` so the asset-id it binds to the ciphertext stays the un-offset `asset_id`.
    fn _points(
        asset_id: AssetId,
        enc_keys: &[Affine<G0>],
        med_keys: &[Affine<G0>],
        params: &AssetCommitmentParams<G0, G1>,
    ) -> Vec<Affine<G0>> {
        iter::once((params.j_0 * (G0::ScalarField::from(asset_id + 1))).into_affine())
            .chain(enc_keys.iter().copied())
            .chain(med_keys.iter().copied())
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
    /// Mediator affirmation keys. These are not shared and each mediator has access to one of the encryption keys.
    /// These keys are whats stored along the asset-id in [`AssetData`] and are hidden from verifier unless explicitly revealed.
    /// A leg cannot have zero encryption keys but non-zero mediator affirmation keys.
    pub med_keys: Vec<G>,
    /// Encryption keys for which [`LegCore`] will be encrypted.
    /// These keys are not stored along the asset-id in [`AssetData`] but provided by the leg creator and are always revealed to the verifier
    pub public_enc_keys: Vec<G>,
}

/// Which of the sender and receiver can decrypt the other's public key.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PartyVisibility {
    /// Neither party can decrypt the other's public key.
    NoVisibility,
    /// Both parties can decrypt the other's public key.
    FullVisibility,
    /// Only the sender can decrypt the receiver's public key.
    OnlySenderSeesReceiver,
    /// Only the receiver can decrypt the sender's public key.
    OnlyReceiverSeesSender,
}

impl PartyVisibility {
    pub fn new(sender_sees_receiver: bool, receiver_sees_sender: bool) -> Self {
        match (sender_sees_receiver, receiver_sees_sender) {
            (false, false) => Self::NoVisibility,
            (true, true) => Self::FullVisibility,
            (true, false) => Self::OnlySenderSeesReceiver,
            (false, true) => Self::OnlyReceiverSeesSender,
        }
    }

    /// Sender can decrypt receiver's pk.
    pub fn sender_sees_receiver(&self) -> bool {
        matches!(self, Self::FullVisibility | Self::OnlySenderSeesReceiver)
    }

    /// Receiver can decrypt sender's pk.
    pub fn receiver_sees_sender(&self) -> bool {
        matches!(self, Self::FullVisibility | Self::OnlyReceiverSeesSender)
    }
}

#[derive(Clone)]
pub struct LegEncConfig {
    /// Which of the sender and receiver can decrypt the other's public key.
    pub visibility: PartyVisibility,
    /// If `true`, asset-id is revealed in the leg else a curve-tree membership proof in the asset
    /// tree is created
    pub reveal_asset_id: bool,
}

impl Default for LegEncConfig {
    /// By default, both parties see each other and the asset-id is hidden.
    fn default() -> Self {
        Self {
            visibility: PartyVisibility::FullVisibility,
            reveal_asset_id: false,
        }
    }
}

/// Twisted Elgamal's ephemeral public key per auditor/mediator `(pk * r_1, pk * r_2, pk * r_3, Option<pk * r_4>)`
/// The last component is `None` when asset-id is revealed.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EphemeralPublicKey<G: AffineRepr> {
    pub r1: G,
    pub r2: G,
    pub r3: G,
    pub r4: Option<G>,
}

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
}

/// Receiver's ephemeral public keys. Index 0 is None when the receiver cannot decrypt the sender's pk.
/// Index 3 is None when asset-id is revealed (not encrypted).
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiverEphemeralPublicKey<G: AffineRepr> {
    pub r1: Option<G>,
    pub r2: G,
    pub r3: G,
    pub r4: Option<G>,
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
    /// This is None when asset-id is revealed as mediator affirmation keys don't need to be hidden.
    /// When no mediators (asset-id hidden), its an empty vec.
    pub r_meds: Option<Vec<F>>,
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionCore<G: AffineRepr> {
    pub ct_s: G,
    pub ct_r: G,
    pub ct_amount: G,
    pub ct_asset_id: AssetIdEncryption<G>,
}

impl<G: AffineRepr> LegEncryptionCore<G> {
    /// Returns the ciphertext for the participant, `ct_s` for sender, `ct_r` for receiver
    pub fn ct_participant(&self, is_sender: bool) -> G {
        if is_sender { self.ct_s } else { self.ct_r }
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

/// Mediator entry: `ct_med = enc_key_gen * mu + K`, `eph_pk_med_keys[k] = enc_keys[k] * mu` for
/// every encryption key `k`.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorEncryption<G: AffineRepr> {
    /// Ephemeral public keys, one per encryption key from [`AssetData`].
    pub eph_pk_med_keys: Vec<G>,
    /// Encryption of the mediator affirmation key.
    pub ct_med: G,
}

impl<F: PrimeField, G: AffineRepr<ScalarField = F>> MediatorEncryption<G> {
    /// Recover the mediator's affirmation key from `ct_med` using the mediator's encryption key
    /// `sk_enc` and its `index` in `eph_pk_med_keys`.
    pub fn affirmation_key(&self, sk_enc: &F, index: usize) -> Result<G> {
        let eph_pk = self
            .eph_pk_med_keys
            .get(index)
            .ok_or(Error::InvalidKeyIndex(index))?;
        let mut sk_enc_inv = sk_enc.inverse().ok_or(Error::InvertingZero)?;
        let r_enc_gen = *eph_pk * sk_enc_inv;
        sk_enc_inv.zeroize();
        Ok((self.ct_med.into_group() - r_enc_gen).into_affine())
    }

    /// First index whose decryption under `sk_enc` equals `affirmation_key`.
    pub fn find_key_index(&self, sk_enc: &F, affirmation_key: &G) -> Result<usize> {
        let mut sk_enc_inv = sk_enc.inverse().ok_or(Error::InvertingZero)?;
        let ct_med = self.ct_med.into_group();
        let idx = self
            .eph_pk_med_keys
            .iter()
            .position(|eph_pk| (ct_med - (*eph_pk * sk_enc_inv)).into_affine() == *affirmation_key);
        sk_enc_inv.zeroize();
        idx.ok_or_else(|| {
            Error::ProofGenerationError("No mediator encryption key matches".to_string())
        })
    }
}

/// Mediator entry of the scheme that predates the broadcast one, where the affirmation key is
/// encrypted to a single encryption key identified by its index in [`AssetData`]. Kept so legs
/// created under that scheme can still be affirmed, using [`crate::leg::mediator::MediatorTxnOldProof`].
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorEncryptionOld<G: AffineRepr> {
    /// The index corresponds to the encryption key from [`AssetData`].
    pub enc_key_index: u8,
    /// Ephemeral encryption public key of the mediator.
    pub eph_pk_med_key: G,
    /// Encryption of the mediator affirmation key. Only the mediator holding the encryption key at
    /// `enc_key_index` needs to decrypt it.
    pub ct_med: G,
}

impl<F: PrimeField, G: AffineRepr<ScalarField = F>> MediatorEncryptionOld<G> {
    /// Recover the mediator's affirmation key from `ct_med` using the mediator's encryption key
    /// `sk_enc` (the secret of the encryption key at `enc_key_index` in [`AssetData`]).
    pub fn affirmation_key(&self, sk_enc: &F) -> Result<G> {
        let mut sk_enc_inv = sk_enc.inverse().ok_or(Error::InvertingZero)?;
        let r_enc_gen = self.eph_pk_med_key * sk_enc_inv;
        sk_enc_inv.zeroize();
        Ok((self.ct_med.into_group() - r_enc_gen).into_affine())
    }
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncCoreAndEphKeys<G: AffineRepr> {
    pub core: LegEncryptionCore<G>,
    pub eph_pk_s: SenderEphemeralPublicKey<G>,
    pub eph_pk_r: ReceiverEphemeralPublicKey<G>,
}

impl<G: AffineRepr> LegEncCoreAndEphKeys<G> {
    /// Which of the sender and receiver can decrypt the other's public key.
    pub fn party_visibility(&self) -> PartyVisibility {
        PartyVisibility::new(self.eph_pk_s.r2.is_some(), self.eph_pk_r.r1.is_some())
    }
}

/// Twisted Elgamal encryption of sender pk, receiver pk, amount and asset id
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryption<G: AffineRepr> {
    pub leg_enc_core_and_eph_keys: LegEncCoreAndEphKeys<G>,
    /// Ephemeral public keys of auditors in the order they appear in [`AssetData`].
    pub eph_pk_enc_keys: Vec<EphemeralPublicKey<G>>,
    /// Ephemeral public keys of auditors in the order they were passed by leg creator.
    pub eph_pk_public_enc_keys: Vec<EphemeralPublicKey<G>>,
    /// This is None when asset-id is revealed. When no mediators, its an empty vec
    pub mediators: Option<Vec<MediatorEncryption<G>>>,
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
        med_keys: Vec<G>,
        public_enc_keys: Vec<G>,
    ) -> Result<Self> {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        {
            if amount > MAX_BALANCE {
                return Err(Error::AmountTooLarge(amount));
            }
            if asset_id > MAX_ASSET_ID {
                return Err(Error::AssetIdTooLarge(asset_id));
            }
            // Not allowing sender and receiver to be the same key to be consistent with non-confidential assets
            if pk_s_e == pk_r_e {
                return Err(Error::SameSenderAndReceiverNotAllowed());
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

        // Per-mediator randomness. Mediator ciphertext are only created when asset-id is hidden.
        let r_meds: Option<Vec<F>> = (!config.reveal_asset_id)
            .then(|| (0..self.med_keys.len()).map(|_| F::rand(rng)).collect());

        let mut proj: Vec<G::Group> = Vec::new();
        proj.push(enc_key_gen * r1 + pk_s_enc); // ct_s
        proj.push(enc_key_gen * r2 + pk_r_enc); // ct_r
        proj.push(enc_key_gen * r3 + enc_gen * amount); // ct_amount
        if !config.reveal_asset_id {
            proj.push(enc_key_gen * r4.unwrap() + enc_gen * asset_id); // ct_asset_id
        }
        proj.push(pk_s_enc * r1); // eph_pk_s.r1
        proj.push(pk_s_enc * r3); // eph_pk_s.r3
        if let Some(r) = r4 {
            proj.push(pk_s_enc * r); // eph_pk_s.r4
        }
        if config.visibility.sender_sees_receiver() {
            proj.push(pk_s_enc * r2); // eph_pk_s.r2 (cross)
        }
        proj.push(pk_r_enc * r2); // eph_pk_r.r2
        proj.push(pk_r_enc * r3); // eph_pk_r.r3
        if let Some(r) = r4 {
            proj.push(pk_r_enc * r); // eph_pk_r.r4
        }
        if config.visibility.receiver_sees_sender() {
            proj.push(pk_r_enc * r1); // eph_pk_r.r1 (cross)
        }
        for pk in self.enc_keys.iter() {
            proj.push(*pk * r1);
            proj.push(*pk * r2);
            proj.push(*pk * r3);
            if let Some(r) = r4 {
                proj.push(*pk * r);
            }
        }
        for pk in self.public_enc_keys.iter() {
            proj.push(*pk * r1);
            proj.push(*pk * r2);
            proj.push(*pk * r3);
            if let Some(r) = r4 {
                proj.push(*pk * r);
            }
        }
        // Mediator entries: one ephemeral per encryption key plus `ct_med`, all in the same batch.
        let med_offset = proj.len();
        let num_enc = self.enc_keys.len();
        if let Some(r_meds) = r_meds.as_ref() {
            for i in 0..self.med_keys.len() {
                for pk in self.enc_keys.iter() {
                    proj.push(*pk * r_meds[i]); // eph_pk_med_keys[k]
                }
                proj.push(enc_key_gen * r_meds[i] + self.med_keys[i]); // ct_med
            }
        }

        let aff = G::Group::normalize_batch(&proj);

        let mut k = 0usize;
        macro_rules! next {
            () => {{
                let v = aff[k];
                k += 1;
                v
            }};
        }

        let ct_s = next!();
        let ct_r = next!();
        let ct_amount = next!();
        let ct_asset_id = if config.reveal_asset_id {
            AssetIdEncryption::Revealed(self.core.asset_id)
        } else {
            AssetIdEncryption::Ciphertext(next!())
        };

        let mut eph_pk_s = SenderEphemeralPublicKey::<G> {
            r1: next!(),
            r2: None,
            r3: next!(),
            r4: (!config.reveal_asset_id).then(|| next!()),
        };
        eph_pk_s.r2 = config.visibility.sender_sees_receiver().then(|| next!());

        let mut eph_pk_r = ReceiverEphemeralPublicKey::<G> {
            r1: None,
            r2: next!(),
            r3: next!(),
            r4: (!config.reveal_asset_id).then(|| next!()),
        };
        eph_pk_r.r1 = config.visibility.receiver_sees_sender().then(|| next!());

        let enc_keys: Vec<EphemeralPublicKey<G>> = self
            .enc_keys
            .iter()
            .map(|_| EphemeralPublicKey::<G> {
                r1: next!(),
                r2: next!(),
                r3: next!(),
                r4: r4.map(|_| next!()),
            })
            .collect();

        let public_enc_keys: Vec<EphemeralPublicKey<G>> = self
            .public_enc_keys
            .iter()
            .map(|_| EphemeralPublicKey::<G> {
                r1: next!(),
                r2: next!(),
                r3: next!(),
                r4: r4.map(|_| next!()),
            })
            .collect();

        debug_assert_eq!(k, med_offset);

        let ct_meds: Option<Vec<MediatorEncryption<G>>> = r_meds.as_ref().map(|_| {
            (0..self.med_keys.len())
                .map(|i| {
                    let base = med_offset + i * (num_enc + 1);
                    MediatorEncryption {
                        eph_pk_med_keys: aff[base..base + num_enc].to_vec(),
                        ct_med: aff[base + num_enc],
                    }
                })
                .collect()
        });

        Zeroize::zeroize(&mut amount);
        Zeroize::zeroize(&mut asset_id);

        Ok((
            LegEncryption {
                leg_enc_core_and_eph_keys: LegEncCoreAndEphKeys {
                    core: LegEncryptionCore {
                        ct_s,
                        ct_r,
                        ct_amount,
                        ct_asset_id,
                    },
                    eph_pk_s,
                    eph_pk_r,
                },
                eph_pk_enc_keys: enc_keys,
                eph_pk_public_enc_keys: public_enc_keys,
                mediators: ct_meds,
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
        self.leg_enc_core_and_eph_keys.core.is_asset_id_revealed()
    }

    /// Which of the sender and receiver can decrypt the other's public key.
    pub fn party_visibility(&self) -> PartyVisibility {
        self.leg_enc_core_and_eph_keys.party_visibility()
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id(&self) -> Option<AssetId> {
        self.leg_enc_core_and_eph_keys.core.asset_id()
    }

    /// `None` when asset-id is revealed (hidden from the verifier).
    pub fn asset_id_ciphertext(&self) -> Option<G> {
        self.leg_enc_core_and_eph_keys.core.asset_id_ciphertext()
    }

    pub fn ct_s(&self) -> G {
        self.leg_enc_core_and_eph_keys.core.ct_s
    }

    pub fn ct_r(&self) -> G {
        self.leg_enc_core_and_eph_keys.core.ct_r
    }

    pub fn ct_amount(&self) -> G {
        self.leg_enc_core_and_eph_keys.core.ct_amount
    }

    /// Returns the ciphertext for the participant, `ct_s` for sender, `ct_r` for receiver
    pub fn ct_participant(&self, is_sender: bool) -> G {
        self.leg_enc_core_and_eph_keys
            .core
            .ct_participant(is_sender)
    }

    /// Number of mediator entries. Zero when asset-id is revealed as no entries are created then;
    /// dispatch on [`LegEncryption::is_asset_id_revealed`] rather than this when the mediator count
    /// of the asset is needed.
    pub fn num_mediators(&self) -> usize {
        self.mediators.as_ref().map(|m| m.len()).unwrap_or(0)
    }

    pub fn mediator_encryption(&self, index: usize) -> Result<&MediatorEncryption<G>> {
        self.mediators
            .as_ref()
            .and_then(|m| m.get(index))
            .ok_or_else(|| Error::MediatorNotFoundAtIndex(index))
    }

    pub fn eph_pk_participant(&self, is_sender: bool) -> G {
        if is_sender {
            self.leg_enc_core_and_eph_keys.eph_pk_s.r1
        } else {
            self.leg_enc_core_and_eph_keys.eph_pk_r.r2
        }
    }

    pub fn eph_pk_and_ct_participant(&self, is_sender: bool) -> (G, G) {
        if is_sender {
            (
                self.leg_enc_core_and_eph_keys.eph_pk_s.r1,
                self.leg_enc_core_and_eph_keys.core.ct_s,
            )
        } else {
            (
                self.leg_enc_core_and_eph_keys.eph_pk_r.r2,
                self.leg_enc_core_and_eph_keys.core.ct_r,
            )
        }
    }

    pub fn eph_pk_asset_id(&self, is_sender: bool) -> Option<G> {
        if is_sender {
            self.leg_enc_core_and_eph_keys.eph_pk_s.r4
        } else {
            self.leg_enc_core_and_eph_keys.eph_pk_r.r4
        }
    }

    pub fn eph_pk_amount(&self, is_sender: bool) -> G {
        if is_sender {
            self.leg_enc_core_and_eph_keys.eph_pk_s.r3
        } else {
            self.leg_enc_core_and_eph_keys.eph_pk_r.r3
        }
    }

    pub fn core_and_eph_keys_for_sender(
        &self,
    ) -> (LegEncryptionCore<G>, SenderEphemeralPublicKey<G>) {
        (
            self.leg_enc_core_and_eph_keys.core.clone(),
            self.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
        )
    }

    pub fn core_and_eph_keys_for_receiver(
        &self,
    ) -> (LegEncryptionCore<G>, ReceiverEphemeralPublicKey<G>) {
        (
            self.leg_enc_core_and_eph_keys.core.clone(),
            self.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
        )
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
    ) -> Result<(G, Option<G>, AssetId, Balance)> {
        self.decrypt_as_sender_with_limits(sk_enc, enc_gen, None, None)
    }

    pub fn decrypt_as_sender_with_limits(
        &self,
        sk_enc: &F,
        enc_gen: G,
        max_asset_id: Option<AssetId>,
        max_amount: Option<Balance>,
    ) -> Result<(G, Option<G>, AssetId, Balance)> {
        let enc_gen = enc_gen.into_group();
        let max_asset_id = max_asset_id.unwrap_or(MAX_ASSET_ID);
        let max_amount = max_amount.unwrap_or(MAX_BALANCE);

        let mut sk_enc_inv = sk_enc
            .inverse()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;

        let asset_id =
            self.decrypt_asset_id_as_participant(true, &sk_enc_inv, enc_gen, max_asset_id)?;

        let amount_pt = Self::decrypt_element_with_sk_inv(
            &sk_enc_inv,
            self.leg_enc_core_and_eph_keys.core.ct_amount,
            self.leg_enc_core_and_eph_keys.eph_pk_s.r3,
        );
        let amount = solve_discrete_log_bsgs::<G::Group>(max_amount, enc_gen, amount_pt)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))?;

        let sender = Self::decrypt_element_with_sk_inv(
            &sk_enc_inv,
            self.leg_enc_core_and_eph_keys.core.ct_s,
            self.leg_enc_core_and_eph_keys.eph_pk_s.r1,
        )
        .into_affine();
        let receiver = self.leg_enc_core_and_eph_keys.eph_pk_s.r2.map(|eph| {
            Self::decrypt_element_with_sk_inv(
                &sk_enc_inv,
                self.leg_enc_core_and_eph_keys.core.ct_r,
                eph,
            )
            .into_affine()
        });
        sk_enc_inv.zeroize();

        Ok((sender, receiver, asset_id, amount))
    }

    /// Decrypt as receiver using `sk_enc`. Receiver can always decrypt own pk, amount, and asset_id
    /// when it was encrypted; returns `None` for asset_id if it was not encrypted (revealed).
    /// Sender pk is only decryptable when `eph_pk_r.0` is present.
    pub fn decrypt_as_receiver(
        &self,
        sk_enc: &F,
        enc_gen: G,
    ) -> Result<(Option<G>, G, AssetId, Balance)> {
        self.decrypt_as_receiver_with_limits(sk_enc, enc_gen, None, None)
    }

    pub fn decrypt_as_receiver_with_limits(
        &self,
        sk_enc: &F,
        enc_gen: G,
        max_asset_id: Option<AssetId>,
        max_amount: Option<Balance>,
    ) -> Result<(Option<G>, G, AssetId, Balance)> {
        let enc_gen = enc_gen.into_group();
        let max_asset_id = max_asset_id.unwrap_or(MAX_ASSET_ID);
        let max_amount = max_amount.unwrap_or(MAX_BALANCE);

        let mut sk_enc_inv = sk_enc
            .inverse()
            .ok_or_else(|| Error::InvalidSecretKey("Inverse failed".into()))?;

        let asset_id =
            self.decrypt_asset_id_as_participant(false, &sk_enc_inv, enc_gen, max_asset_id)?;

        let amount_pt = Self::decrypt_element_with_sk_inv(
            &sk_enc_inv,
            self.leg_enc_core_and_eph_keys.core.ct_amount,
            self.leg_enc_core_and_eph_keys.eph_pk_r.r3,
        );
        let amount = solve_discrete_log_bsgs::<G::Group>(max_amount, enc_gen, amount_pt)
            .ok_or_else(|| Error::DecryptionFailed("Discrete log of `amount` failed.".into()))?;

        let receiver = Self::decrypt_element_with_sk_inv(
            &sk_enc_inv,
            self.leg_enc_core_and_eph_keys.core.ct_r,
            self.leg_enc_core_and_eph_keys.eph_pk_r.r2,
        )
        .into_affine();
        let sender = self.leg_enc_core_and_eph_keys.eph_pk_r.r1.map(|eph| {
            Self::decrypt_element_with_sk_inv(
                &sk_enc_inv,
                self.leg_enc_core_and_eph_keys.core.ct_s,
                eph,
            )
            .into_affine()
        });
        sk_enc_inv.zeroize();

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
    ) -> Result<(G, G, AssetId, Balance)> {
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
    ) -> Result<(G, G, AssetId, Balance)> {
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

        let sender = Self::decrypt_as_group_element(
            &sk_inv,
            self.leg_enc_core_and_eph_keys.core.ct_s,
            eph_keys[key_index].r1,
        );
        let receiver = Self::decrypt_as_group_element(
            &sk_inv,
            self.leg_enc_core_and_eph_keys.core.ct_r,
            eph_keys[key_index].r2,
        );

        Zeroize::zeroize(&mut sk_inv);

        Ok((
            sender.into_affine(),
            receiver.into_affine(),
            asset_id,
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
    ) -> Result<AssetId> {
        let eph_keys = if is_public {
            &self.eph_pk_public_enc_keys
        } else {
            &self.eph_pk_enc_keys
        };
        if key_index >= eph_keys.len() {
            return Err(Error::InvalidKeyIndex(key_index));
        }

        match &self.leg_enc_core_and_eph_keys.core.ct_asset_id {
            AssetIdEncryption::Revealed(id) => Ok(*id as AssetId),
            AssetIdEncryption::Ciphertext(ct) => {
                let asset_id =
                    Self::decrypt_as_group_element(sk_inv, *ct, eph_keys[key_index].r4.unwrap());
                solve_discrete_log_bsgs::<G::Group>(max_asset_id as _, enc_gen, asset_id)
                    .map(|id| id as AssetId)
                    .ok_or_else(|| {
                        Error::DecryptionFailed("Discrete log of `asset_id` failed.".into())
                    })
            }
        }
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
        let amount = Self::decrypt_as_group_element(
            sk_inv,
            self.leg_enc_core_and_eph_keys.core.ct_amount,
            eph_keys[key_index].r3,
        );

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
    ) -> Result<AssetId> {
        let eph_pk = self.eph_pk_asset_id(is_sender);
        match &self.leg_enc_core_and_eph_keys.core.ct_asset_id {
            AssetIdEncryption::Revealed(id) => Ok(*id as AssetId),
            AssetIdEncryption::Ciphertext(ct) => {
                let eph_pk_asset_id = eph_pk.ok_or_else(|| {
                    Error::DecryptionFailed("Missing ephemeral key for asset ID decryption".into())
                })?;
                let asset_id_pt =
                    Self::decrypt_element_with_sk_inv(&sk_enc_inv, *ct, eph_pk_asset_id);
                solve_discrete_log_bsgs::<G::Group>(max_asset_id as u64, enc_gen, asset_id_pt)
                    .ok_or_else(|| {
                        Error::DecryptionFailed("Discrete log of `asset_id` failed.".into())
                    })
                    .map(|id| id as AssetId)
            }
        }
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
