use crate::keys::{DecKey, EncKey};
use crate::util::{
    initialize_curve_tree_prover, initialize_curve_tree_verifier, prove_with_rng, verify_with_rng,
};
use crate::{AMOUNT_BITS, AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::aliases::FullDigest;
use dock_crypto_utils::commitment::PedersenCommitmentKey;
use dock_crypto_utils::elgamal::Ciphertext;
use dock_crypto_utils::hashing_utils::hash_to_field;
use dock_crypto_utils::solve_discrete_log::solve_discrete_log_bsgs_alt;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::{CryptoRng, RngCore};
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use std::ops::Neg;
use std::time::{Duration, Instant};

pub const SK_EPH_GEN_LABEL: &[u8; 20] = b"ephemeral-secret-key";

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct Leg<G: AffineRepr> {
    /// Public key of sender
    pub pk_s: G,
    /// Public key of receiver
    pub pk_r: G,
    /// Public key of mediator if asset has a mediator. If asset has auditor then its None.
    pub pk_m: Option<G>,
    pub amount: Balance,
    pub asset_id: AssetId,
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryption<G: AffineRepr> {
    /// Ciphertext for sender public key
    pub ct_s: Ciphertext<G>,
    /// Ciphertext for receiver public key
    pub ct_r: Ciphertext<G>,
    /// Ciphertext for mediator public key if asset has a mediator. If asset has auditor then its None.
    pub ct_m: Option<Ciphertext<G>>,
    pub ct_amount: Ciphertext<G>,
    pub ct_asset_id: Ciphertext<G>,
    // TODO: Do i need version here as each leg is part of a txn and txn will have version information
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionRandomness<G: AffineRepr>(
    pub G::ScalarField,
    pub G::ScalarField,
    pub Option<G::ScalarField>,
    pub G::ScalarField,
    pub G::ScalarField,
);

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EphemeralSkEncryption<G: AffineRepr> {
    /// Encrypted message. Called `Y = g * r + h * m` in report
    pub encrypted: G,
    /// For sender pk. Constructed as `pk_s * r`
    pub key_s: G,
    /// For receiver pk. Constructed as `pk_r * r`
    pub key_r: G,
    /// For mediator/auditor pk. Constructed as `pk_m * r` or `pk_a * r`
    pub key_m_a: G,
}

impl<G: AffineRepr> Leg<G> {
    pub fn new(pk_s: G, pk_r: G, pk_m: Option<G>, amount: Balance, asset_id: AssetId) -> Self {
        assert!(amount <= MAX_AMOUNT);
        assert!(asset_id <= MAX_ASSET_ID);
        Self {
            pk_s,
            pk_r,
            pk_m,
            amount,
            asset_id,
        }
    }

    /// `enc_sig_gen` should be the same as used in creating both the encryption key and signing (affirmation) key
    /// as its assumed that both keys use the same generator.
    /// `asset_value_gen` is used for Elgamal enc. of value and asset-id while leg encryption.
    /// `enc_sig_gen -> g, asset_value_gen -> h` in report.
    pub fn encrypt<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        pk_e: &G,
        enc_sig_gen: G,
        asset_value_gen: G,
    ) -> (LegEncryption<G>, LegEncryptionRandomness<G>) {
        let r1 = G::ScalarField::rand(rng);
        let r2 = G::ScalarField::rand(rng);
        // Encrypt mediator key if it exists
        let (r3, ct_m) = if let Some(pk_m) = self.pk_m {
            let r3 = G::ScalarField::rand(rng);
            let ct_m = Ciphertext::new_given_randomness(&pk_m, &r3, pk_e, &enc_sig_gen);
            (Some(r3), Some(ct_m))
        } else {
            (None, None)
        };
        let r4 = G::ScalarField::rand(rng);
        let r5 = G::ScalarField::rand(rng);

        // TODO: This is not constant time. Fix
        let v = (asset_value_gen * G::ScalarField::from(self.amount)).into_affine();
        let asset_id = (asset_value_gen * G::ScalarField::from(self.asset_id)).into_affine();
        // TODO: Use new_given_randomness_and_window_tables
        let enc = LegEncryption {
            ct_s: Ciphertext::new_given_randomness(&self.pk_s, &r1, pk_e, &enc_sig_gen),
            ct_r: Ciphertext::new_given_randomness(&self.pk_r, &r2, pk_e, &enc_sig_gen),
            ct_m,
            ct_amount: Ciphertext::new_given_randomness(&v, &r4, pk_e, &enc_sig_gen),
            ct_asset_id: Ciphertext::new_given_randomness(&asset_id, &r5, pk_e, &enc_sig_gen),
        };
        (enc, LegEncryptionRandomness(r1, r2, r3, r4, r5))
    }
}

impl<G: AffineRepr> EphemeralSkEncryption<G> {
    /// `pk_a_m` is the encryption key of the mediator or the auditor
    /// Generator `enc_gen` should be the same as used in creating encryption key. `enc_gen -> g` in report.
    /// Generator `h` is a generator to anything else in this code.
    pub fn new<R: RngCore + CryptoRng, D: FullDigest>(
        rng: &mut R,
        pk_s: G,
        pk_r: G,
        pk_a_m: G,
        enc_gen: G,
        h: G,
    ) -> (Self, G::ScalarField, DecKey<G>, EncKey<G>) {
        // Use twisted-Elgamal encryption.
        // Generate random k and then [(pk_s * k), (pk_r * k), (pk_a_m * k), (g*k + h*pre_sk_e)]
        // Hash h*pre_sk_e to get the ephemeral secret key sk_e, ephemeral public key is g*sk_e

        let k = G::ScalarField::rand(rng);
        let pre_sk_e = G::ScalarField::rand(rng);
        let h_p = h * pre_sk_e;
        let encrypted = ((enc_gen * k) + h_p).into_affine();
        let key_s = (pk_s * k).into_affine();
        let key_r = (pk_r * k).into_affine();
        let key_m_a = (pk_a_m * k).into_affine();

        let mut h_p_bytes = vec![];
        h_p.into_affine()
            .serialize_compressed(&mut h_p_bytes)
            .unwrap();
        let sk_e = hash_to_field::<G::ScalarField, D>(SK_EPH_GEN_LABEL, &h_p_bytes);
        let pk_e = (enc_gen * sk_e).into_affine();
        (
            Self {
                encrypted,
                key_s,
                key_r,
                key_m_a,
            },
            k,
            DecKey(sk_e),
            EncKey(pk_e),
        )
    }

    pub fn decrypt_for_sender<D: FullDigest>(&self, sk: G::ScalarField) -> G::ScalarField {
        self.decrypt::<D>(sk, self.key_s)
    }

    pub fn decrypt_for_receiver<D: FullDigest>(&self, sk: G::ScalarField) -> G::ScalarField {
        self.decrypt::<D>(sk, self.key_r)
    }

    pub fn decrypt_for_mediator_or_auditor<D: FullDigest>(
        &self,
        sk: G::ScalarField,
    ) -> G::ScalarField {
        self.decrypt::<D>(sk, self.key_m_a)
    }

    fn decrypt<D: FullDigest>(&self, sk: G::ScalarField, enc_key: G) -> G::ScalarField {
        let g_k = (enc_key * sk.inverse().unwrap()).into_affine();
        let h_p = (self.encrypted.into_group() - g_k).into_affine();
        let mut h_p_bytes = vec![];
        h_p.serialize_compressed(&mut h_p_bytes).unwrap();
        hash_to_field::<G::ScalarField, D>(SK_EPH_GEN_LABEL, &h_p_bytes)
    }
}

impl<G: AffineRepr> LegEncryption<G> {
    pub fn decrypt(&self, sk_e: &G::ScalarField, asset_value_gen: G) -> Leg<G> {
        let pk_s = self.ct_s.decrypt(sk_e);
        let pk_r = self.ct_r.decrypt(sk_e);
        let pk_m = self.ct_m.as_ref().map(|ct_m| ct_m.decrypt(sk_e));
        let amount = self.ct_amount.decrypt(sk_e);
        let asset_id = self.ct_asset_id.decrypt(sk_e);
        let base = asset_value_gen.into_group();
        let amount = solve_discrete_log_bsgs_alt(MAX_AMOUNT, base, amount.into_group()).unwrap();
        let asset_id =
            solve_discrete_log_bsgs_alt(MAX_ASSET_ID as u64, base, asset_id.into_group()).unwrap();
        Leg {
            pk_m,
            pk_s,
            pk_r,
            amount,
            asset_id: asset_id as u32,
        }
    }
}

/// Given commitment key `leaf_comm_key`, the leaf is `leaf_comm_key[0] * role + leaf_comm_key[1] * asset_id + pk`
/// where `role` equals 1 if `pk` is the public key of mediator else its 0.A
pub fn create_leaf_for_asset_tree<G: AffineRepr>(
    asset_id: AssetId,
    pk: G,
    is_mediator: bool,
    leaf_comm_key: &[G],
) -> G {
    // TODO: Add version and leaf_comm_key should have another generator
    assert!(leaf_comm_key.len() >= 2);
    (if is_mediator {
        leaf_comm_key[0]
    } else {
        G::zero()
    } + (leaf_comm_key[1] * G::ScalarField::from(asset_id))
        + pk)
        .into_affine()
}

/// Create leg and ephemeral keys. Encrypt leg and ephemeral secret key.
/// Called by venue when it intends to create a settlement.
/// `enc_sig_gen` should be the same as used in creating both the encryption key and signing (affirmation) key
/// as its assumed that both keys use the same generator.
/// `asset_value_gen` is used for Elgamal enc. of value and asset-id while leg encryption.
/// `enc_sig_gen -> g, asset_value_gen -> h` in report.
pub fn initialize_leg_for_settlement<R: RngCore + CryptoRng, G: AffineRepr, D: FullDigest>(
    rng: &mut R,
    asset_id: AssetId,
    amount: Balance,
    pk_s: (G, G),
    pk_r: (G, G),
    pk_m: Option<(G, G)>,
    pk_a: Option<G>,
    enc_sig_gen: G,
    asset_value_gen: G,
) -> (
    Leg<G>,
    LegEncryption<G>,
    LegEncryptionRandomness<G>,
    EphemeralSkEncryption<G>,
    G::ScalarField,
    DecKey<G>,
    EncKey<G>,
) {
    assert!(pk_a.is_some() ^ pk_m.is_some());
    let (pk_a_m, pk_m) = if pk_m.is_some() {
        let pk_m = pk_m.unwrap();
        (pk_m.1, Some(pk_m.0))
    } else {
        (pk_a.unwrap(), None)
    };
    // Create ephemeral encryption keypair and encrypt ephemeral sk for each party
    // Passing `asset_value_gen` to `EphemeralSkEncryption::new` is incidental and could be a new generator as well.
    let (eph_ek_enc, eph_ek_enc_r, sk_e, pk_e) = EphemeralSkEncryption::new::<_, D>(
        rng,
        pk_s.1,
        pk_r.1,
        pk_a_m,
        enc_sig_gen,
        asset_value_gen,
    );
    // Create leg and encrypt it for ephemeral pk
    let leg = Leg::new(pk_s.0, pk_r.0, pk_m, amount, asset_id);
    let (leg_enc, leg_enc_rand) = leg.encrypt(rng, &pk_e.0, enc_sig_gen, asset_value_gen);
    (
        leg,
        leg_enc,
        leg_enc_rand,
        eph_ek_enc,
        eph_ek_enc_r,
        sk_e,
        pk_e,
    )
}

pub const SETTLE_TXN_ODD_LABEL: &[u8; 24] = b"settlement-txn-odd-level";
pub const SETTLE_TXN_EVEN_LABEL: &[u8; 25] = b"settlement-txn-even-level";
pub const SETTLE_TXN_CHALLENGE_LABEL: &[u8; 24] = b"settlement-txn-challenge";
pub const SETTLE_TXN_INSTANCE_LABEL: &[u8; 29] = b"settlement-txn-extra-instance";

pub const MEDIATOR_TXN_LABEL: &[u8; 12] = b"mediator-txn";
pub const MEDIATOR_TXN_RESPONSE_LABEL: &[u8; 17] = b"mediator-response";
pub const MEDIATOR_TXN_ACCEPT_RESPONSE: &[u8; 6] = b"accept";
pub const MEDIATOR_TXN_REJECT_RESPONSE: &[u8; 6] = b"reject";
pub const MEDIATOR_TXN_CHALLENGE_LABEL: &[u8; 22] = b"mediator-txn-challenge";
pub const MEDIATOR_TXN_INSTANCE_LABEL: &[u8; 27] = b"mediator-txn-extra-instance";

/// Proofs when the asset has an auditor.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuditorEncProofs<G: AffineRepr> {
    /// Pedersen commitment to randomness used in twisted Elgamal encryption of ephemeral secret key
    pub K_1: G,
    /// Pedersen commitment to asset-id
    pub K_2: G,
    /// Pedersen commitment to product of asset-id and randomness used in twisted Elgamal encryption of ephemeral secret key
    pub K_3: G,
    /// For proving knowledge of opening of `K_1`
    pub resp_K_1: PokPedersenCommitment<G>,
    /// For proving knowledge of opening of `K_2`
    pub resp_K_2: PokPedersenCommitment<G>,
    /// For proving knowledge of opening of `K_3`
    pub resp_K_3: PokPedersenCommitment<G>,
    /// For proving knowledge of witness (asset-id) in relation between `K_1` and `K_3`
    pub resp_K_3_K_1: PokDiscreteLog<G>,
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
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// Commitment to amount
    pub comm_amount: Affine<G0>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of ephemeral secret key in ephemeral public key
    /// using Schnorr protocol (step 1 and 3 of Schnorr). Only present when settlement has mediator
    pub resp_eph_pk: Option<PokDiscreteLog<Affine<G0>>>,
    /// Only present when asset has auditor
    pub auditor_enc_proofs: Option<AuditorEncProofs<Affine<G0>>>,
    /// Commitment to randomness and response for proving knowledge of amount using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to amount is created for using with Bulletproofs
    pub resp_amount: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of randomness in Elgamal encryption of amount.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_amount_enc_0: PokDiscreteLog<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of ephemeral secret key and amount in Elgamal encryption of amount.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_amount_enc_1: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of randomness in Elgamal encryption of asset-id.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_asset_id_enc_0: PokDiscreteLog<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of ephemeral secret key and amount in Elgamal encryption of asset-id.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_asset_id_enc_1: PokPedersenCommitment<Affine<G0>>,
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

    /// `eph_sk_enc_rand` is the randomness created during twisted-Elgamal encryption of ephemeral secret key
    /// and `eph_pk` is the ephemeral public key
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<Affine<G0>>,
        eph_sk_enc: EphemeralSkEncryption<Affine<G0>>,
        eph_sk_enc_rand: F0,
        eph_pk: Affine<G0>,
        auditor_enc_key: Option<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        // Rest are public parameters
        tree_parameters: &SelRerandParameters<G0, G1>,
        leaf_comm_key: &[Affine<G0>],
        enc_sig_gen: Affine<G0>,
        asset_value_gen: Affine<G0>,
        ped_comm_key: &PedersenCommitmentKey<Affine<G0>>,
    ) -> Self {
        assert!(
            (leg.pk_m.is_some() && leg_enc.ct_m.is_some() && leg_enc_rand.2.is_some())
                || (leg.pk_m.is_none() && leg_enc.ct_m.is_none() && auditor_enc_key.is_some())
        );

        let is_mediator_present = leg_enc.ct_m.is_some();

        let minus_leaf_comm_key = leaf_comm_key[1].neg();
        let minus_B_blinding = tree_parameters.even_parameters.pc_gens.B_blinding.neg();

        let (mut even_prover, odd_prover, re_randomized_path, rerandomization) =
            initialize_curve_tree_prover(
                rng,
                SETTLE_TXN_EVEN_LABEL,
                SETTLE_TXN_ODD_LABEL,
                leaf_path,
                tree_parameters,
            );

        let mut leg_instance = vec![];
        leg_enc.serialize_compressed(&mut leg_instance).unwrap();
        eph_sk_enc.serialize_compressed(&mut leg_instance).unwrap();
        nonce.serialize_compressed(&mut leg_instance).unwrap();
        tree_parameters
            .serialize_compressed(&mut leg_instance)
            .unwrap();
        leaf_comm_key
            .serialize_compressed(&mut leg_instance)
            .unwrap();
        enc_sig_gen.serialize_compressed(&mut leg_instance).unwrap();
        asset_value_gen
            .serialize_compressed(&mut leg_instance)
            .unwrap();
        // TODO: Hash comm_amount and re_randomized_path as well

        even_prover
            .transcript()
            .append_message_without_static_label(SETTLE_TXN_INSTANCE_LABEL, &leg_instance);

        let r_amount = F0::rand(rng);
        // TODO: Can I avoid this new commitment?
        let (comm_amount, var_amount) = even_prover.commit(F0::from(leg.amount), r_amount);

        // TODO: What if we do range proof outside circuit? Or using another protocol like Bulletproofs++?
        range_proof(
            &mut even_prover,
            var_amount.into(),
            Some(leg.amount),
            AMOUNT_BITS.into(),
        )
        .unwrap();

        // Blinding (for Schnorr) for the randomness used in Elgamal encryption of mediator key in leg encryption
        let r_a_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let amount_blinding = F0::rand(rng);
        // Blinding (for Schnorr) for randomness used in Elgamal encryption of asset-id in leg encryption
        let enc_amount_blinding = F0::rand(rng);
        // Blinding (for Schnorr) for randomness used in Elgamal encryption of amount in leg encryption
        let enc_asset_id_blinding = F0::rand(rng);

        let at = F0::from(leg.asset_id);

        // Proving that mediator/auditor pk pk_A_M, is in leaf and in mediator/auditor pk's encryption
        // leaf = (leaf_comm_key[0] * role) + (leaf_comm_key[1] * asset_id) + pk_A_M
        // randomized leaf r_leaf = (leaf_comm_key[0] * role) + (leaf_comm_key[1] * asset_id) + pk_A_M + (B_blinding * rerandomization)

        let (t_r_leaf, t_eph_pk, for_auditor_enc_proofs) = if is_mediator_present {
            // When settlement has mediator

            // Notation: `enc_sig_gen` denotes `enc_sig_gen`

            // Since we have Elgamal encryption of mediator pk as (g * r, (pk_e * r) + pk_M)) as (C0, C1),
            // we substitute C1 - (pk_e * r) for pk_M in r_leaf to get
            // r_leaf = (leaf_comm_key[0] * role) + (leaf_comm_key[1] * asset_id) + C1 - (pk_e * r) + (B_blinding * rerandomization)
            // Now role = 1 and r_leaf and C1 is known so we need to prove knowledge of relation
            // (pk_e * r) + (-leaf_comm_key[1] * asset_id) + (-B_blinding * rerandomization) = C1 - r_leaf + leaf_comm_key[0]
            let t_r_leaf = SchnorrCommitment::new(
                &[eph_pk, minus_leaf_comm_key, minus_B_blinding],
                vec![r_a_blinding, asset_id_blinding, F0::rand(rng)],
            );

            // For proving knowledge of randomness used in encryption of mediator key in leg encryption. For relation: g * r = ct_m.eph_pk
            let t_eph_pk =
                PokDiscreteLogProtocol::init(leg_enc_rand.2.unwrap(), r_a_blinding, &enc_sig_gen);
            (t_r_leaf, Some(t_eph_pk), None)
        } else {
            // When settlement has auditor

            // For auditor pk pk_A and role = 0,
            // r_leaf = (leaf_comm_key[1] * asset_id) + pk_A + (B_blinding * rerandomization)
            // r_leaf + (-leaf_comm_key[1] * asset_id) + (-B_blinding * rerandomization) = pk_A
            // For twisted Elgamal encryption of sk_e, we have X_a = pk_A * k
            // (r_leaf + (-leaf_comm_key[1] * asset_id) + (-B_blinding * rerandomization)) * k = X_a
            // (r_leaf * k) + (-leaf_comm_key[1] * (asset_id * k)) + (-B_blinding * (rerandomization * k)) = X_a
            // Since r_leaf, leaf_comm_key[1], leaf_comm_key[1] and X_a are public, we use sigma protocol to prove correctness of above relation

            // Let j_2, j_3 be generators as in code they are belong to `ped_comm_key`. k is called `eph_sk_enc_rand` in code.

            // The idea is to create 3 elements as $K_1 = j_2 * k + j_3 * r_k, K_2 = j_2 * at + j_3 * r_{at}, K_3 = j_2*{at.k} + j_3*{at.r_k}$,
            // prove the product relation between these 3 while proving that exponent of $j_2$ in $K_3$ is same as
            // the exponent of $-j_1$ in $X_A$, the exponent of $j_2$ in $K_1$ is same as the exponent of r_leaf in $X_A$ and similarly
            // for $at$.
            // Note that $K_3$ is intentionally created as $K_1 * at$ for efficiency.
            //
            // So the 5 relations that need to be proven (for auditor only)
            // 1. r_leaf*k + (-j_1)*{at.k}+(-B)*{t.k} = X_A$
            // 2. $K_1 = j_2 * k + j_3 * r_k$
            // 3. $K_2 = j_2 * at + j_3 * r_{at}$
            // 4. $K_3 = j_2*{at.k} + j_3*{at.r_k}$
            // 5. $K_3 = K_1*{at}$

            let k_blinding = F0::rand(rng);
            let k_times_asset_id_blinding = F0::rand(rng);

            let t_r_leaf = SchnorrCommitment::new(
                &[
                    re_randomized_path.re_randomized_leaf,
                    minus_leaf_comm_key,
                    minus_B_blinding,
                ],
                vec![k_blinding, k_times_asset_id_blinding, F0::rand(rng)],
            );

            let r_k = F0::rand(rng);
            let r_asset_id = F0::rand(rng);
            let K_1 = ped_comm_key.commit(&eph_sk_enc_rand, &r_k);
            let K_2 = ped_comm_key.commit(&at, &r_asset_id);
            let K_3 = ped_comm_key.commit(&(at * eph_sk_enc_rand), &(at * r_k));

            debug_assert_eq!((K_1 * at).into_affine(), K_3);

            let t_K_1 = PokPedersenCommitmentProtocol::init(
                eph_sk_enc_rand,
                k_blinding,
                &ped_comm_key.g,
                r_k,
                F0::rand(rng),
                &ped_comm_key.h,
            );
            let t_K_2 = PokPedersenCommitmentProtocol::init(
                at,
                asset_id_blinding,
                &ped_comm_key.g,
                r_asset_id,
                F0::rand(rng),
                &ped_comm_key.h,
            );
            let t_K_3 = PokPedersenCommitmentProtocol::init(
                at * eph_sk_enc_rand,
                k_times_asset_id_blinding,
                &ped_comm_key.g,
                at * r_k,
                F0::rand(rng),
                &ped_comm_key.h,
            );
            let t_K_3_K_1 = PokDiscreteLogProtocol::init(at, asset_id_blinding, &K_1);

            (
                t_r_leaf,
                None,
                Some((K_1, K_2, K_3, t_K_1, t_K_2, t_K_3, t_K_3_K_1)),
            )
        };

        // Proving correctness of amount in the commitment used with Bulletproofs
        let t_amount = PokPedersenCommitmentProtocol::init(
            leg.amount.into(),
            amount_blinding,
            &tree_parameters.even_parameters.pc_gens.B,
            r_amount,
            F0::rand(rng),
            &tree_parameters.even_parameters.pc_gens.B_blinding,
        );

        // Proving correctness of Elgamal encryption of amount
        let t_amount_enc_0 =
            PokDiscreteLogProtocol::init(leg_enc_rand.3, enc_amount_blinding, &enc_sig_gen);
        let t_amount_enc_1 = PokPedersenCommitmentProtocol::init(
            leg_enc_rand.3,
            enc_amount_blinding,
            &eph_pk,
            leg.amount.into(),
            amount_blinding,
            &asset_value_gen,
        );

        // Proving correctness of Elgamal encryption of asset-id
        let t_asset_id_enc_0 =
            PokDiscreteLogProtocol::init(leg_enc_rand.4, enc_asset_id_blinding, &enc_sig_gen);
        let t_asset_id_enc_1 = PokPedersenCommitmentProtocol::init(
            leg_enc_rand.4,
            enc_asset_id_blinding,
            &eph_pk,
            leg.asset_id.into(),
            asset_id_blinding,
            &asset_value_gen,
        );

        let mut prover_transcript = even_prover.transcript();

        if is_mediator_present {
            t_eph_pk
                .as_ref()
                .unwrap()
                .challenge_contribution(
                    &enc_sig_gen,
                    &leg_enc.ct_m.as_ref().unwrap().eph_pk,
                    &mut prover_transcript,
                )
                .unwrap();
        } else {
            let (K_1, K_2, K_3, t_K_1, t_K_2, t_K_3, t_K_3_K_1) =
                for_auditor_enc_proofs.as_ref().unwrap();
            K_1.serialize_compressed(&mut prover_transcript).unwrap();
            K_2.serialize_compressed(&mut prover_transcript).unwrap();
            K_3.serialize_compressed(&mut prover_transcript).unwrap();
            t_K_1
                .challenge_contribution(
                    &ped_comm_key.g,
                    &ped_comm_key.h,
                    &K_1,
                    &mut prover_transcript,
                )
                .unwrap();
            t_K_2
                .challenge_contribution(
                    &ped_comm_key.g,
                    &ped_comm_key.h,
                    &K_2,
                    &mut prover_transcript,
                )
                .unwrap();
            t_K_3
                .challenge_contribution(
                    &ped_comm_key.g,
                    &ped_comm_key.h,
                    &K_3,
                    &mut prover_transcript,
                )
                .unwrap();
            t_K_3_K_1
                .challenge_contribution(&K_1, &K_3, &mut prover_transcript)
                .unwrap();
        }
        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_amount
            .challenge_contribution(
                &tree_parameters.even_parameters.pc_gens.B,
                &tree_parameters.even_parameters.pc_gens.B_blinding,
                &comm_amount,
                &mut prover_transcript,
            )
            .unwrap();
        t_amount_enc_0
            .challenge_contribution(
                &enc_sig_gen,
                &leg_enc.ct_amount.eph_pk,
                &mut prover_transcript,
            )
            .unwrap();
        t_amount_enc_1
            .challenge_contribution(
                &eph_pk,
                &asset_value_gen,
                &leg_enc.ct_amount.encrypted,
                &mut prover_transcript,
            )
            .unwrap();
        t_asset_id_enc_0
            .challenge_contribution(
                &enc_sig_gen,
                &leg_enc.ct_asset_id.eph_pk,
                &mut prover_transcript,
            )
            .unwrap();
        t_asset_id_enc_1
            .challenge_contribution(
                &eph_pk,
                &asset_value_gen,
                &leg_enc.ct_asset_id.encrypted,
                &mut prover_transcript,
            )
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        // TODO: Eliminate duplicate responses
        let (resp_leaf, resp_eph_pk, auditor_enc_proofs) = if is_mediator_present {
            let resp_leaf = t_r_leaf
                .response(
                    &[
                        leg_enc_rand.2.unwrap(),
                        leg.asset_id.into(),
                        rerandomization,
                    ],
                    &prover_challenge,
                )
                .unwrap();
            (
                resp_leaf,
                Some(t_eph_pk.unwrap().gen_proof(&prover_challenge)),
                None,
            )
        } else {
            let (K_1, K_2, K_3, t_K_1, t_K_2, t_K_3, t_K_3_K_1) = for_auditor_enc_proofs.unwrap();
            let proofs = AuditorEncProofs {
                K_1,
                K_2,
                K_3,
                resp_K_1: t_K_1.gen_proof(&prover_challenge),
                resp_K_2: t_K_2.gen_proof(&prover_challenge),
                resp_K_3: t_K_3.gen_proof(&prover_challenge),
                resp_K_3_K_1: t_K_3_K_1.gen_proof(&prover_challenge),
            };
            let resp_leaf = t_r_leaf
                .response(
                    &[
                        eph_sk_enc_rand,
                        at * eph_sk_enc_rand,
                        rerandomization * eph_sk_enc_rand,
                    ],
                    &prover_challenge,
                )
                .unwrap();
            (resp_leaf, None, Some(proofs))
        };
        let resp_amount = t_amount.gen_proof(&prover_challenge);
        let resp_amount_enc_0 = t_amount_enc_0.clone().gen_proof(&prover_challenge);
        let resp_amount_enc_1 = t_amount_enc_1.clone().gen_proof(&prover_challenge);
        let resp_asset_id_enc_0 = t_asset_id_enc_0.clone().gen_proof(&prover_challenge);
        let resp_asset_id_enc_1 = t_asset_id_enc_1.clone().gen_proof(&prover_challenge);

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &tree_parameters, rng).unwrap();

        Self {
            even_proof,
            odd_proof,
            re_randomized_path,
            comm_amount,
            t_r_leaf: t_r_leaf.t,
            resp_leaf,
            resp_eph_pk,
            auditor_enc_proofs,
            resp_amount,
            resp_amount_enc_0,
            resp_amount_enc_1,
            resp_asset_id_enc_0,
            resp_asset_id_enc_1,
        }
    }

    #[cfg(feature = "std")]
    pub fn verify(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        eph_sk_enc: EphemeralSkEncryption<Affine<G0>>,
        eph_pk: Affine<G0>,
        tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        tree_parameters: &SelRerandParameters<G0, G1>,
        leaf_comm_key: &[Affine<G0>],
        enc_sig_gen: Affine<G0>,
        asset_value_gen: Affine<G0>,
        ped_comm_key: &PedersenCommitmentKey<Affine<G0>>,
    ) -> Result<(), R1CSError> {
        let mut rng = rand::thread_rng();
        self.verify_with_rng(
            leg_enc,
            eph_sk_enc,
            eph_pk,
            tree_root,
            nonce,
            tree_parameters,
            leaf_comm_key,
            enc_sig_gen,
            asset_value_gen,
            ped_comm_key,
            &mut rng,
        )
    }

    pub fn verify_with_rng<R: RngCore + CryptoRng>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        eph_sk_enc: EphemeralSkEncryption<Affine<G0>>,
        eph_pk: Affine<G0>,
        tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        tree_parameters: &SelRerandParameters<G0, G1>,
        leaf_comm_key: &[Affine<G0>],
        enc_sig_gen: Affine<G0>,
        asset_value_gen: Affine<G0>,
        ped_comm_key: &PedersenCommitmentKey<Affine<G0>>,
        rng: &mut R,
    ) -> Result<(), R1CSError> {
        let is_mediator_present = leg_enc.ct_m.is_some();

        if is_mediator_present {
            assert!(self.resp_eph_pk.is_some());
        } else {
            assert!(self.auditor_enc_proofs.is_some());
        }

        let minus_leaf_comm_key = leaf_comm_key[1].neg();
        let minus_B_blinding = tree_parameters.even_parameters.pc_gens.B_blinding.neg();

        let (mut even_verifier, odd_verifier) = initialize_curve_tree_verifier(
            SETTLE_TXN_EVEN_LABEL,
            SETTLE_TXN_ODD_LABEL,
            self.re_randomized_path.clone(),
            tree_root,
            tree_parameters,
        );

        let mut leg_instance = vec![];
        leg_enc.serialize_compressed(&mut leg_instance).unwrap();
        eph_sk_enc.serialize_compressed(&mut leg_instance).unwrap();
        nonce.serialize_compressed(&mut leg_instance).unwrap();
        tree_parameters
            .serialize_compressed(&mut leg_instance)
            .unwrap();
        leaf_comm_key
            .serialize_compressed(&mut leg_instance)
            .unwrap();
        enc_sig_gen.serialize_compressed(&mut leg_instance).unwrap();
        asset_value_gen
            .serialize_compressed(&mut leg_instance)
            .unwrap();

        even_verifier
            .transcript()
            .append_message_without_static_label(SETTLE_TXN_INSTANCE_LABEL, &leg_instance);

        let var_amount = even_verifier.commit(self.comm_amount);
        // Value is of 48-bit
        range_proof(
            &mut even_verifier,
            var_amount.into(),
            None,
            AMOUNT_BITS.into(),
        )
        .unwrap();

        let mut verifier_transcript = even_verifier.transcript();

        let mut dur = Duration::default();
        let mut size = 0;
        if is_mediator_present {
            self.resp_eph_pk
                .as_ref()
                .unwrap()
                .challenge_contribution(
                    &enc_sig_gen,
                    &leg_enc.ct_m.as_ref().unwrap().eph_pk,
                    &mut verifier_transcript,
                )
                .unwrap();
        } else {
            let clock = Instant::now();
            let aud_proofs = self.auditor_enc_proofs.as_ref().unwrap();
            aud_proofs
                .K_1
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            aud_proofs
                .K_2
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            aud_proofs
                .K_3
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            aud_proofs
                .resp_K_1
                .challenge_contribution(
                    &ped_comm_key.g,
                    &ped_comm_key.h,
                    &aud_proofs.K_1,
                    &mut verifier_transcript,
                )
                .unwrap();
            aud_proofs
                .resp_K_2
                .challenge_contribution(
                    &ped_comm_key.g,
                    &ped_comm_key.h,
                    &aud_proofs.K_2,
                    &mut verifier_transcript,
                )
                .unwrap();
            aud_proofs
                .resp_K_3
                .challenge_contribution(
                    &ped_comm_key.g,
                    &ped_comm_key.h,
                    &aud_proofs.K_3,
                    &mut verifier_transcript,
                )
                .unwrap();
            aud_proofs
                .resp_K_3_K_1
                .challenge_contribution(&aud_proofs.K_1, &aud_proofs.K_3, &mut verifier_transcript)
                .unwrap();
            dur += clock.elapsed();
            size = aud_proofs.compressed_size();
        }
        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_amount
            .challenge_contribution(
                &tree_parameters.even_parameters.pc_gens.B,
                &tree_parameters.even_parameters.pc_gens.B_blinding,
                &self.comm_amount,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_amount_enc_0
            .challenge_contribution(
                &enc_sig_gen,
                &leg_enc.ct_amount.eph_pk,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_amount_enc_1
            .challenge_contribution(
                &eph_pk,
                &asset_value_gen,
                &&leg_enc.ct_amount.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_asset_id_enc_0
            .challenge_contribution(
                &enc_sig_gen,
                &leg_enc.ct_asset_id.eph_pk,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_asset_id_enc_1
            .challenge_contribution(
                &eph_pk,
                &asset_value_gen,
                &&leg_enc.ct_asset_id.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        if is_mediator_present {
            let ct_m = leg_enc.ct_m.as_ref().unwrap();
            assert!(self.resp_eph_pk.as_ref().unwrap().verify(
                &ct_m.eph_pk,
                &enc_sig_gen,
                &verifier_challenge
            ));
            // Verify proof of knowledge of opening of leaf commitment and mediator's key encryption (in leg)
            let y = (ct_m.encrypted - self.re_randomized_path.re_randomized_leaf
                + leaf_comm_key[0])
                .into_affine();
            self.resp_leaf
                .is_valid(
                    &[eph_pk, minus_leaf_comm_key, minus_B_blinding],
                    &y,
                    &self.t_r_leaf,
                    &verifier_challenge,
                )
                .unwrap();
        } else {
            let clock = Instant::now();
            let aud_proofs = self.auditor_enc_proofs.as_ref().unwrap();
            self.resp_leaf
                .is_valid(
                    &[
                        self.re_randomized_path.re_randomized_leaf,
                        minus_leaf_comm_key,
                        minus_B_blinding,
                    ],
                    &eph_sk_enc.key_m_a,
                    &self.t_r_leaf,
                    &verifier_challenge,
                )
                .unwrap();
            assert!(aud_proofs.resp_K_1.verify(
                &aud_proofs.K_1,
                &ped_comm_key.g,
                &ped_comm_key.h,
                &verifier_challenge,
            ));
            assert!(aud_proofs.resp_K_2.verify(
                &aud_proofs.K_2,
                &ped_comm_key.g,
                &ped_comm_key.h,
                &verifier_challenge,
            ));
            assert!(aud_proofs.resp_K_3.verify(
                &aud_proofs.K_3,
                &ped_comm_key.g,
                &ped_comm_key.h,
                &verifier_challenge,
            ));
            assert!(aud_proofs.resp_K_3_K_1.verify(
                &aud_proofs.K_3,
                &aud_proofs.K_1,
                &verifier_challenge,
            ));
            dur += clock.elapsed();
        }

        assert!(self.resp_amount.verify(
            &self.comm_amount,
            &tree_parameters.even_parameters.pc_gens.B,
            &tree_parameters.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(self.resp_amount_enc_0.verify(
            &leg_enc.ct_amount.eph_pk,
            &enc_sig_gen,
            &verifier_challenge
        ));
        assert!(self.resp_amount_enc_1.verify(
            &leg_enc.ct_amount.encrypted,
            &eph_pk,
            &asset_value_gen,
            &verifier_challenge
        ));
        assert!(self.resp_asset_id_enc_0.verify(
            &leg_enc.ct_asset_id.eph_pk,
            &enc_sig_gen,
            &verifier_challenge
        ));
        assert!(self.resp_asset_id_enc_1.verify(
            &leg_enc.ct_asset_id.encrypted,
            &eph_pk,
            &asset_value_gen,
            &verifier_challenge
        ));

        // Amount is same
        assert_eq!(self.resp_amount.response1, self.resp_amount_enc_1.response2);
        if is_mediator_present {
            // enc randomness is same in leaf as in auditor pk encryption
            assert_eq!(
                self.resp_leaf.0[0],
                self.resp_eph_pk.as_ref().unwrap().response
            );
            // Asset id is same
            assert_eq!(self.resp_leaf.0[1], self.resp_asset_id_enc_1.response2);
        } else {
            let aud_proofs = self.auditor_enc_proofs.as_ref().unwrap();
            // Enc randomness for twisted Elgamal is same
            assert_eq!(self.resp_leaf.0[0], aud_proofs.resp_K_1.response1);
            // Asset id is same
            assert_eq!(
                self.resp_asset_id_enc_1.response2,
                aud_proofs.resp_K_2.response1
            );
            assert_eq!(
                self.resp_asset_id_enc_1.response2,
                aud_proofs.resp_K_3_K_1.response
            );
            // Product of enc randomness and asset id is same
            assert_eq!(self.resp_leaf.0[1], aud_proofs.resp_K_3.response1);
        }

        verify_with_rng(
            even_verifier,
            odd_verifier,
            &self.even_proof,
            &self.odd_proof,
            &tree_parameters,
            rng,
        )?;
        log::info!("Time and size: {:?}, {}", dur, size);
        Ok(())
    }
}

/// This is the proof for mediator affirm/reject. Report section 5.1.12
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorTxnProof<G: AffineRepr> {
    /// Commitment to randomness and response for proving knowledge of secret key mediator's public key encryption.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_enc_pk: PokPedersenCommitment<G>,
}

impl<G: AffineRepr> MediatorTxnProof<G> {
    /// `sig_gen` is the generator used when creating signing key. `sig_gen -> g` in report.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        eph_sk: G::ScalarField,
        eph_pk: G,
        mediator_sk: G::ScalarField,
        accept: bool,
        nonce: &[u8],
        sig_gen: G,
    ) -> Self {
        assert!(leg_enc.ct_m.is_some());
        let ct_m = leg_enc.ct_m.as_ref().unwrap();

        let mut prover_transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        // Need to prove that mediator knows its secret key in the encryption of its public key

        // TODO: Should generator for ephemeral encryption key and account key be different?
        let t_enc_pk = PokPedersenCommitmentProtocol::init(
            eph_sk,
            G::ScalarField::rand(rng),
            &ct_m.eph_pk,
            mediator_sk,
            G::ScalarField::rand(rng),
            &sig_gen,
        );
        t_enc_pk
            .challenge_contribution(
                &ct_m.eph_pk,
                &sig_gen,
                &ct_m.encrypted,
                &mut prover_transcript,
            )
            .unwrap();

        // Hash the mediator's response
        if accept {
            prover_transcript
                .append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            prover_transcript
                .append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let mut extra_instance = vec![];
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        eph_pk.serialize_compressed(&mut extra_instance).unwrap();
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        sig_gen.serialize_compressed(&mut extra_instance).unwrap();

        prover_transcript
            .append_message_without_static_label(MEDIATOR_TXN_INSTANCE_LABEL, &extra_instance);

        let prover_challenge =
            prover_transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

        let resp_enc_pk = t_enc_pk.gen_proof(&prover_challenge);
        Self { resp_enc_pk }
    }

    /// `sig_gen` is the generator used when creating signing key. `sig_gen -> g` in report.
    pub fn verify(
        &self,
        leg_enc: LegEncryption<G>,
        eph_pk: G,
        accept: bool,
        nonce: &[u8],
        sig_gen: G,
    ) -> Result<(), R1CSError> {
        assert!(leg_enc.ct_m.is_some());
        let ct_m = leg_enc.ct_m.as_ref().unwrap();

        let mut verifier_transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

        self.resp_enc_pk
            .challenge_contribution(
                &ct_m.eph_pk,
                &sig_gen,
                &ct_m.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();

        // Verifier should also hash the mediator's response
        if accept {
            verifier_transcript
                .append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            verifier_transcript
                .append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let mut extra_instance = vec![];
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        eph_pk.serialize_compressed(&mut extra_instance).unwrap();
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        sig_gen.serialize_compressed(&mut extra_instance).unwrap();

        verifier_transcript
            .append_message_without_static_label(MEDIATOR_TXN_INSTANCE_LABEL, &extra_instance);

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_CHALLENGE_LABEL);

        assert!(self.resp_enc_pk.verify(
            &ct_m.encrypted,
            &ct_m.eph_pk,
            &sig_gen,
            &verifier_challenge
        ));
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::keys::{SigKey, VerKey, keygen_enc, keygen_sig};
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
    use std::time::Instant;
    use test_log::test;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type PallasFr = ark_pallas::Fr;

    /// Generate account signing and encryption keys for all sender, receiver, and auditor.
    /// This is just for testing and in practice, each party generates its own keys.
    pub fn setup_keys<R: RngCore + CryptoRng, G: AffineRepr>(
        rng: &mut R,
        g: G,
    ) -> (
        ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
        ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
        ((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>)),
    ) {
        // Account signing (affirmation) keys
        let (sk_s, pk_s) = keygen_sig(rng, g);
        let (sk_r, pk_r) = keygen_sig(rng, g);
        let (sk_a, pk_a) = keygen_sig(rng, g);

        // Encryption keys
        let (sk_s_e, pk_s_e) = keygen_enc(rng, g);
        let (sk_r_e, pk_r_e) = keygen_enc(rng, g);
        let (sk_a_e, pk_a_e) = keygen_enc(rng, g);
        (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        )
    }

    #[test]
    fn leg_verification_with_mediator() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;

        // Create public params (generators, etc)
        let asset_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        let comm_key = PedersenCommitmentKey::<PallasA>::new::<Blake2b512>(b"test");

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let leaf_comm_key = vec![PallasA::rand(&mut rng), PallasA::rand(&mut rng)];

        // All parties generate their keys
        let (
            ((_sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((_sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((_sk_m, pk_m), (sk_m_e, pk_m_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;

        // Mediator key with asset id is added to the tree
        let leaf = create_leaf_for_asset_tree(asset_id, pk_m.0, true, &leaf_comm_key);
        assert_eq!(
            leaf,
            (leaf_comm_key[0] + (leaf_comm_key[1] * PallasFr::from(asset_id)) + pk_m.0)
                .into_affine()
        );

        let set = vec![leaf];
        let asset_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &asset_tree_params,
            Some(2),
        );

        // Setup ends.
        let amount = 100;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let (leg, leg_enc, leg_enc_rand, eph_sk_enc, eph_sk_enc_rand, sk_e, pk_e) =
            initialize_leg_for_settlement::<_, _, Blake2b512>(
                &mut rng,
                asset_id,
                amount,
                (pk_s.0, pk_s_e.0),
                (pk_r.0, pk_r_e.0),
                Some((pk_m.0, pk_m_e.0)),
                None,
                gen_p_1,
                gen_p_2,
            );

        // Venue gets the leaf path from the tree
        let path = asset_tree.get_path_to_leaf_for_proof(0, 0);

        // Verifier gets the root of the tree
        let root = asset_tree.root_node();

        let proof = SettlementTxnProof::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand,
            eph_sk_enc.clone(),
            eph_sk_enc_rand,
            pk_e.0,
            None,
            path,
            nonce,
            &asset_tree_params,
            &leaf_comm_key,
            gen_p_1,
            gen_p_2,
            &comm_key,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc.clone(),
                eph_sk_enc.clone(),
                pk_e.0,
                &root,
                nonce,
                &asset_tree_params,
                &leaf_comm_key,
                gen_p_1,
                gen_p_2,
                &comm_key,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        assert!(proof.resp_eph_pk.is_some());
        assert!(proof.auditor_enc_proofs.is_none());

        log::info!(
            "total proof size = {}",
            proof.compressed_size()
                + leg_enc.compressed_size()
                + eph_sk_enc.compressed_size()
                + pk_e.0.compressed_size()
        );
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );

        // All parties decrypt to the same ephemeral secret key
        assert_eq!(
            eph_sk_enc.decrypt_for_sender::<Blake2b512>(sk_s_e.0),
            sk_e.0
        );
        assert_eq!(
            eph_sk_enc.decrypt_for_receiver::<Blake2b512>(sk_r_e.0),
            sk_e.0
        );
        assert_eq!(
            eph_sk_enc.decrypt_for_mediator_or_auditor::<Blake2b512>(sk_m_e.0),
            sk_e.0
        );

        // Leg can be decrypted with ephemeral secret key
        assert_eq!(leg_enc.decrypt(&sk_e.0, gen_p_2), leg)
    }

    #[test]
    fn leg_verification_with_auditor() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 1024;

        // Create public params (generators, etc)
        let asset_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        let comm_key = PedersenCommitmentKey::<PallasA>::new::<Blake2b512>(b"test");

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let leaf_comm_key = vec![PallasA::rand(&mut rng), PallasA::rand(&mut rng)];

        // All parties generate their keys
        let (
            ((_sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((_sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;

        // Auditor key with asset id is added to the tree
        let leaf = create_leaf_for_asset_tree(asset_id, pk_a_e.0, false, &leaf_comm_key);
        assert_eq!(
            leaf,
            ((leaf_comm_key[1] * PallasFr::from(asset_id)) + pk_a_e.0).into_affine()
        );

        let set = vec![leaf];
        let asset_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &asset_tree_params,
            Some(2),
        );

        // Setup ends.
        let amount = 100;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let (leg, leg_enc, leg_enc_rand, eph_sk_enc, eph_sk_enc_rand, sk_e, pk_e) =
            initialize_leg_for_settlement::<_, _, Blake2b512>(
                &mut rng,
                asset_id,
                amount,
                (pk_s.0, pk_s_e.0),
                (pk_r.0, pk_r_e.0),
                None,
                Some(pk_a_e.0),
                gen_p_1,
                gen_p_2,
            );

        // Venue gets the leaf path from the tree
        let path = asset_tree.get_path_to_leaf_for_proof(0, 0);

        // Verifier gets the root of the tree
        let root = asset_tree.root_node();

        let proof = SettlementTxnProof::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand,
            eph_sk_enc.clone(),
            eph_sk_enc_rand,
            pk_e.0,
            Some(pk_a_e.0),
            path,
            nonce,
            &asset_tree_params,
            &leaf_comm_key,
            gen_p_1,
            gen_p_2,
            &comm_key,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc.clone(),
                eph_sk_enc.clone(),
                pk_e.0,
                &root,
                nonce,
                &asset_tree_params,
                &leaf_comm_key,
                gen_p_1,
                gen_p_2,
                &comm_key,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        assert!(proof.resp_eph_pk.is_none());
        assert!(proof.auditor_enc_proofs.is_some());

        log::info!(
            "total proof size = {}",
            proof.compressed_size()
                + leg_enc.compressed_size()
                + eph_sk_enc.compressed_size()
                + pk_e.0.compressed_size()
        );
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );

        // All parties decrypt to the same ephemeral secret key
        assert_eq!(
            eph_sk_enc.decrypt_for_sender::<Blake2b512>(sk_s_e.0),
            sk_e.0
        );
        assert_eq!(
            eph_sk_enc.decrypt_for_receiver::<Blake2b512>(sk_r_e.0),
            sk_e.0
        );
        assert_eq!(
            eph_sk_enc.decrypt_for_mediator_or_auditor::<Blake2b512>(sk_a_e.0),
            sk_e.0
        );

        // Leg can be decrypted with ephemeral secret key
        assert_eq!(leg_enc.decrypt(&sk_e.0, gen_p_2), leg)
    }

    #[test]
    fn mediator_action() {
        let mut rng = rand::thread_rng();

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);

        let (
            ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;
        let amount = 100;

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let (_leg, leg_enc, _leg_enc_rand, _, _, sk_e, pk_e) =
            initialize_leg_for_settlement::<_, _, Blake2b512>(
                &mut rng,
                asset_id,
                amount,
                (pk_s.0, pk_s_e.0),
                (pk_r.0, pk_r_e.0),
                Some((pk_a.0, pk_a_e.0)),
                None,
                gen_p_1,
                gen_p_2,
            );

        let nonce = b"test-nonce";

        // Mediator "accept"ing in this case
        let accept = true;

        let clock = Instant::now();
        let proof = MediatorTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            sk_e.0,
            pk_e.0,
            sk_a.0,
            accept,
            nonce,
            gen_p_1,
        );
        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(leg_enc.clone(), pk_e.0, accept, nonce, gen_p_1)
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("proof size = {}", proof.compressed_size());
        log::info!(
            "prover time = {:?}, verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }
}
