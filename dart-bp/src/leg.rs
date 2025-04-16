use crate::old::keys::{DecKey, EncKey, keygen_enc};
use crate::{AMOUNT_BITS, AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use blake2::Blake2b512;
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSError, R1CSProof, Verifier};
use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::range_proof;
use digest::Digest;
use dock_crypto_utils::aliases::FullDigest;
use dock_crypto_utils::elgamal::{Ciphertext, HashedElgamalCiphertext};
use dock_crypto_utils::solve_discrete_log::solve_discrete_log_bsgs_alt;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand::RngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use std::ops::Neg;

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct Leg<G: AffineRepr> {
    pub pk_s: G,
    pub pk_r: G,
    pub pk_a: G,
    pub amount: Balance,
    pub asset_id: AssetId,
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryption<G: AffineRepr> {
    pub ct_s: Ciphertext<G>,
    pub ct_r: Ciphertext<G>,
    pub ct_a: Ciphertext<G>,
    pub ct_amount: Ciphertext<G>,
    pub ct_asset_id: Ciphertext<G>,
    // TODO: Do i need version here as each leg is part of a txn and txn will have version information
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionRandomness<G: AffineRepr>(
    pub G::ScalarField,
    pub G::ScalarField,
    pub G::ScalarField,
    pub G::ScalarField,
    pub G::ScalarField,
);

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EphemeralSkEncryption<G: AffineRepr> {
    pub eph_pk: G,
    pub encrypted_sk_for_sender: G::ScalarField,
    pub encrypted_sk_for_receiver: G::ScalarField,
    pub encrypted_sk_for_auditor: G::ScalarField,
}

impl<G: AffineRepr> Leg<G> {
    pub fn new(pk_s: G, pk_r: G, pk_a: G, amount: Balance, asset_id: AssetId) -> Self {
        assert!(amount <= MAX_AMOUNT);
        assert!(asset_id <= MAX_ASSET_ID);
        Self {
            pk_s,
            pk_r,
            pk_a,
            amount,
            asset_id,
        }
    }

    pub fn encrypt<R: RngCore>(
        &self,
        rng: &mut R,
        pk_e: &G,
        g: G,
        h: G,
    ) -> (LegEncryption<G>, LegEncryptionRandomness<G>) {
        let r1 = G::ScalarField::rand(rng);
        let r2 = G::ScalarField::rand(rng);
        let r3 = G::ScalarField::rand(rng);
        let r4 = G::ScalarField::rand(rng);
        let r5 = G::ScalarField::rand(rng);
        let v = (h * G::ScalarField::from(self.amount)).into_affine();
        let asset_id = (h * G::ScalarField::from(self.asset_id)).into_affine();
        // TODO: Use new_given_randomness_and_window_tables
        let enc = LegEncryption {
            ct_s: Ciphertext::new_given_randomness(&self.pk_s, &r1, pk_e, &g),
            ct_r: Ciphertext::new_given_randomness(&self.pk_r, &r2, pk_e, &g),
            ct_a: Ciphertext::new_given_randomness(&self.pk_a, &r3, pk_e, &g),
            ct_amount: Ciphertext::new_given_randomness(&v, &r4, pk_e, &g),
            ct_asset_id: Ciphertext::new_given_randomness(&asset_id, &r5, pk_e, &g),
        };
        (enc, LegEncryptionRandomness(r1, r2, r3, r4, r5))
    }
}

impl<G: AffineRepr> EphemeralSkEncryption<G> {
    pub fn new<R: RngCore, D: FullDigest>(
        rng: &mut R,
        sk_e: G::ScalarField,
        pk_s: G,
        pk_r: G,
        pk_a: G,
        g: G,
    ) -> (Self, G::ScalarField) {
        let k = G::ScalarField::rand(rng);
        let eph_pk = (g * k).into_affine();
        let shared_key_s = (pk_s * k).into_affine();
        let shared_key_r = (pk_r * k).into_affine();
        let shared_key_a = (pk_a * k).into_affine();
        let encrypted_sk_for_sender = HashedElgamalCiphertext::otp::<D>(shared_key_s) + sk_e;
        let encrypted_sk_for_receiver = HashedElgamalCiphertext::otp::<D>(shared_key_r) + sk_e;
        let encrypted_sk_for_auditor = HashedElgamalCiphertext::otp::<D>(shared_key_a) + sk_e;
        (
            Self {
                eph_pk,
                encrypted_sk_for_sender,
                encrypted_sk_for_receiver,
                encrypted_sk_for_auditor,
            },
            k,
        )
    }

    pub fn decrypt_for_sender<D: FullDigest>(&self, sk: G::ScalarField) -> G::ScalarField {
        self.decrypt::<D>(sk, self.encrypted_sk_for_sender)
    }

    pub fn decrypt_for_receiver<D: FullDigest>(&self, sk: G::ScalarField) -> G::ScalarField {
        self.decrypt::<D>(sk, self.encrypted_sk_for_receiver)
    }

    pub fn decrypt_for_auditor<D: FullDigest>(&self, sk: G::ScalarField) -> G::ScalarField {
        self.decrypt::<D>(sk, self.encrypted_sk_for_auditor)
    }

    fn decrypt<D: FullDigest>(&self, sk: G::ScalarField, enc: G::ScalarField) -> G::ScalarField {
        let shared_key = (self.eph_pk * sk).into_affine();
        enc - HashedElgamalCiphertext::otp::<D>(shared_key)
    }
}

impl<G: AffineRepr> LegEncryption<G> {
    pub fn decrypt(&self, sk_e: &G::ScalarField, h: G) -> Leg<G> {
        let pk_s = self.ct_s.decrypt(sk_e);
        let pk_r = self.ct_r.decrypt(sk_e);
        let pk_a = self.ct_a.decrypt(sk_e);
        let amount = self.ct_amount.decrypt(sk_e);
        let asset_id = self.ct_asset_id.decrypt(sk_e);
        let base = h.into_group();
        let amount = solve_discrete_log_bsgs_alt(MAX_AMOUNT, base, amount.into_group()).unwrap();
        let asset_id =
            solve_discrete_log_bsgs_alt(MAX_ASSET_ID as u64, base, asset_id.into_group()).unwrap();
        Leg {
            pk_a,
            pk_s,
            pk_r,
            amount,
            asset_id: asset_id as u32,
        }
    }
}

pub fn create_leaf_for_auditor_tree<G: AffineRepr>(
    asset_id: AssetId,
    auditor_pk: G,
    leaf_comm_key: G,
) -> G {
    // TODO: Add version and leaf_comm_key should have another generator
    (auditor_pk + (leaf_comm_key * G::ScalarField::from(asset_id))).into_affine()
}

/// Create leg and ephemeral keys. Encrypt leg and ephemeral secret key
pub fn initialize_leg_for_settlement<R: RngCore, G: AffineRepr, D: FullDigest>(
    rng: &mut R,
    asset_id: AssetId,
    amount: Balance,
    pk_s: (G, G),
    pk_r: (G, G),
    pk_a: (G, G),
    g: G,
    h: G,
) -> (
    Leg<G>,
    LegEncryption<G>,
    LegEncryptionRandomness<G>,
    EphemeralSkEncryption<G>,
    G::ScalarField,
    DecKey<G>,
    EncKey<G>,
) {
    let (sk_e, pk_e) = keygen_enc::<_, G>(rng, g);
    // Create leg and encrypt it for ephemeral pk
    let leg = Leg::new(pk_s.0, pk_r.0, pk_a.0, amount, asset_id);
    let (leg_enc, leg_enc_rand) = leg.encrypt(rng, &pk_e.0, g, h);
    // Encrypt ephemeral sk for each party
    let (eph_ek_enc, eph_ek_enc_r) =
        EphemeralSkEncryption::new::<_, D>(rng, sk_e.0, pk_s.1, pk_r.1, pk_a.1, g);
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

pub const AUDITOR_TXN_LABEL: &[u8; 11] = b"auditor-txn";
pub const AUDITOR_TXN_RESPONSE_LABEL: &[u8; 16] = b"auditor-response";
pub const AUDITOR_TXN_ACCEPT_RESPONSE: &[u8; 6] = b"accept";
pub const AUDITOR_TXN_REJECT_RESPONSE: &[u8; 6] = b"reject";
pub const AUDITOR_TXN_CHALLENGE_LABEL: &[u8; 21] = b"auditor-txn-challenge";
pub const AUDITOR_TXN_INSTANCE_LABEL: &[u8; 26] = b"auditor-txn-extra-instance";

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
    pub re_randomized_leaf: Affine<G0>,
    pub comm_amount: Affine<G0>,
    pub t_r_leaf: Affine<G0>,
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    pub resp_eph_pk: PokDiscreteLog<Affine<G0>>,
    pub resp_amount: PokPedersenCommitment<Affine<G0>>,
    pub resp_amount_enc_0: PokDiscreteLog<Affine<G0>>,
    pub resp_amount_enc_1: PokPedersenCommitment<Affine<G0>>,
    pub resp_asset_id_enc_0: PokDiscreteLog<Affine<G0>>,
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
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<Affine<G0>>,
        eph_sk_enc: EphemeralSkEncryption<Affine<G0>>,
        eph_pk: Affine<G0>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        tree_parameters: &SelRerandParameters<G0, G1>,
        leaf_comm_key: Affine<G0>,
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> (Self, F0) {
        // outputting challenge just for debugging
        let minus_leaf_comm_key = leaf_comm_key.neg();
        let minus_B_blinding = tree_parameters.even_parameters.pc_gens.B_blinding.neg();

        let even_transcript = MerlinTranscript::new(SETTLE_TXN_EVEN_LABEL);
        let mut even_prover: Prover<_, Affine<G0>> =
            Prover::new(&tree_parameters.even_parameters.pc_gens, even_transcript);

        let odd_transcript = MerlinTranscript::new(SETTLE_TXN_ODD_LABEL);
        let mut odd_prover: Prover<_, Affine<G1>> =
            Prover::new(&tree_parameters.odd_parameters.pc_gens, odd_transcript);

        let (mut re_randomized_path, rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget(
                &mut even_prover,
                &mut odd_prover,
                tree_parameters,
                rng,
            );
        // path.selected_commitment is the commitment to the coordinates of pk
        let re_randomized_leaf = re_randomized_path.selected_commitment;

        let mut leg_instance = vec![];
        leg_enc.serialize_compressed(&mut leg_instance).unwrap();
        eph_sk_enc.serialize_compressed(&mut leg_instance).unwrap();
        nonce.serialize_compressed(&mut leg_instance).unwrap();
        // TODO: Uncomment
        // tree_parameters.serialize_compressed(&mut leg_instance).unwrap();
        leaf_comm_key
            .serialize_compressed(&mut leg_instance)
            .unwrap();
        g.serialize_compressed(&mut leg_instance).unwrap();
        h.serialize_compressed(&mut leg_instance).unwrap();

        // TODO: Should i hash comm_amount and re_randomized_path as well?

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

        let r_a_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let amount_blinding = F0::rand(rng);
        let enc_amount_blinding = F0::rand(rng);
        let enc_asset_id_blinding = F0::rand(rng);

        let t_eph_pk = PokDiscreteLogProtocol::init(leg_enc_rand.2, r_a_blinding, &g);
        // Proving that auditor pk is in leaf and auditor pk encryption
        let t_r_leaf = SchnorrCommitment::new(
            &[eph_pk, minus_leaf_comm_key, minus_B_blinding],
            vec![r_a_blinding, asset_id_blinding, F0::rand(rng)],
        );
        let t_amount = PokPedersenCommitmentProtocol::init(
            leg.amount.into(),
            amount_blinding,
            &tree_parameters.even_parameters.pc_gens.B,
            r_amount,
            F0::rand(rng),
            &tree_parameters.even_parameters.pc_gens.B_blinding,
        );

        let t_amount_enc_0 = PokDiscreteLogProtocol::init(leg_enc_rand.3, enc_amount_blinding, &g);
        let t_amount_enc_1 = PokPedersenCommitmentProtocol::init(
            leg_enc_rand.3,
            enc_amount_blinding,
            &eph_pk,
            leg.amount.into(),
            amount_blinding,
            &h,
        );

        let t_asset_id_enc_0 =
            PokDiscreteLogProtocol::init(leg_enc_rand.4, enc_asset_id_blinding, &g);
        let t_asset_id_enc_1 = PokPedersenCommitmentProtocol::init(
            leg_enc_rand.4,
            enc_asset_id_blinding,
            &eph_pk,
            leg.asset_id.into(),
            asset_id_blinding,
            &h,
        );

        let mut prover_transcript = even_prover.transcript();

        t_eph_pk
            .challenge_contribution(&g, &leg_enc.ct_a.eph_pk, &mut prover_transcript)
            .unwrap();
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
            .challenge_contribution(&g, &leg_enc.ct_amount.eph_pk, &mut prover_transcript)
            .unwrap();
        t_amount_enc_1
            .challenge_contribution(
                &eph_pk,
                &h,
                &leg_enc.ct_amount.encrypted,
                &mut prover_transcript,
            )
            .unwrap();
        t_asset_id_enc_0
            .challenge_contribution(&g, &leg_enc.ct_asset_id.eph_pk, &mut prover_transcript)
            .unwrap();
        t_asset_id_enc_1
            .challenge_contribution(
                &eph_pk,
                &h,
                &leg_enc.ct_asset_id.encrypted,
                &mut prover_transcript,
            )
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        // TODO: Eliminate duplicate responses
        let resp_eph_pk = t_eph_pk.gen_proof(&prover_challenge);
        let resp_leaf = t_r_leaf
            .response(
                &[leg_enc_rand.2, leg.asset_id.into(), rerandomization],
                &prover_challenge,
            )
            .unwrap();
        let resp_amount = t_amount.gen_proof(&prover_challenge);
        let resp_amount_enc_0 = t_amount_enc_0.clone().gen_proof(&prover_challenge);
        let resp_amount_enc_1 = t_amount_enc_1.clone().gen_proof(&prover_challenge);
        let resp_asset_id_enc_0 = t_asset_id_enc_0.clone().gen_proof(&prover_challenge);
        let resp_asset_id_enc_1 = t_asset_id_enc_1.clone().gen_proof(&prover_challenge);

        let even_proof = even_prover
            .prove(&tree_parameters.even_parameters.bp_gens)
            .unwrap();
        let odd_proof = odd_prover
            .prove(&tree_parameters.odd_parameters.bp_gens)
            .unwrap();

        (
            Self {
                even_proof,
                odd_proof,
                re_randomized_path,
                re_randomized_leaf,
                comm_amount,
                t_r_leaf: t_r_leaf.t,
                resp_leaf,
                resp_eph_pk,
                resp_amount,
                resp_amount_enc_0,
                resp_amount_enc_1,
                resp_asset_id_enc_0,
                resp_asset_id_enc_1,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        eph_sk_enc: EphemeralSkEncryption<Affine<G0>>,
        eph_pk: Affine<G0>,
        tree: &CurveTree<L, 1, G0, G1>,
        prover_challenge: F0,
        nonce: &[u8],
        tree_parameters: &SelRerandParameters<G0, G1>,
        leaf_comm_key: Affine<G0>,
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> Result<(), R1CSError> {
        let minus_leaf_comm_key = leaf_comm_key.neg();
        let minus_B_blinding = tree_parameters.even_parameters.pc_gens.B_blinding.neg();

        let even_transcript = MerlinTranscript::new(SETTLE_TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(SETTLE_TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

        let mut re_randomized_path = self.re_randomized_path.clone();
        tree.select_and_rerandomize_verification_commitments(&mut re_randomized_path);
        let commitments = re_randomized_path.clone();

        // Enforce constraints for odd level
        commitments.odd_verifier_gadget(&mut odd_verifier, &tree_parameters, &tree);

        // Enforce constraints for even level
        commitments.even_verifier_gadget(&mut even_verifier, &tree_parameters, &tree);

        let mut leg_instance = vec![];
        leg_enc.serialize_compressed(&mut leg_instance).unwrap();
        eph_sk_enc.serialize_compressed(&mut leg_instance).unwrap();
        nonce.serialize_compressed(&mut leg_instance).unwrap();
        // TODO: Uncomment
        // tree_parameters.serialize_compressed(&mut leg_instance).unwrap();
        leaf_comm_key
            .serialize_compressed(&mut leg_instance)
            .unwrap();
        g.serialize_compressed(&mut leg_instance).unwrap();
        h.serialize_compressed(&mut leg_instance).unwrap();

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

        self.resp_eph_pk
            .challenge_contribution(&g, &leg_enc.ct_a.eph_pk, &mut verifier_transcript)
            .unwrap();
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
            .challenge_contribution(&g, &leg_enc.ct_amount.eph_pk, &mut verifier_transcript)
            .unwrap();
        self.resp_amount_enc_1
            .challenge_contribution(
                &eph_pk,
                &h,
                &&leg_enc.ct_amount.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_asset_id_enc_0
            .challenge_contribution(&g, &leg_enc.ct_asset_id.eph_pk, &mut verifier_transcript)
            .unwrap();
        self.resp_asset_id_enc_1
            .challenge_contribution(
                &eph_pk,
                &h,
                &&leg_enc.ct_asset_id.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        assert!(
            self.resp_eph_pk
                .verify(&leg_enc.ct_a.eph_pk, &g, &verifier_challenge)
        );
        // Verify proof of knowledge of leaf commitment and leg encryption
        let y = (leg_enc.ct_a.encrypted - self.re_randomized_leaf).into_affine();
        self.resp_leaf
            .is_valid(
                &[eph_pk, minus_leaf_comm_key, minus_B_blinding],
                &y,
                &self.t_r_leaf,
                &verifier_challenge,
            )
            .unwrap();

        assert!(self.resp_amount.verify(
            &self.comm_amount,
            &tree_parameters.even_parameters.pc_gens.B,
            &tree_parameters.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(
            self.resp_amount_enc_0
                .verify(&leg_enc.ct_amount.eph_pk, &g, &verifier_challenge)
        );
        assert!(self.resp_amount_enc_1.verify(
            &leg_enc.ct_amount.encrypted,
            &eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_asset_id_enc_0.verify(
            &leg_enc.ct_asset_id.eph_pk,
            &g,
            &verifier_challenge
        ));
        assert!(self.resp_asset_id_enc_1.verify(
            &leg_enc.ct_asset_id.encrypted,
            &eph_pk,
            &h,
            &verifier_challenge
        ));

        // Asset id is same
        assert_eq!(self.resp_leaf.0[1], self.resp_asset_id_enc_1.response2);
        // Amount is same
        assert_eq!(self.resp_amount.response1, self.resp_amount_enc_1.response2);
        // enc randomness is same in leaf as in auditor pk encryption
        assert_eq!(self.resp_leaf.0[0], self.resp_eph_pk.response);

        even_verifier.verify(
            &self.even_proof,
            &tree_parameters.even_parameters.pc_gens,
            &tree_parameters.even_parameters.bp_gens,
        )?;
        odd_verifier.verify(
            &self.odd_proof,
            &tree_parameters.odd_parameters.pc_gens,
            &tree_parameters.odd_parameters.bp_gens,
        )?;
        Ok(())
    }
}

/// This is the proof for auditor affirm/reject. Report section 5.1.12
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AuditorTxnProof<G: AffineRepr> {
    pub resp_enc_pk: PokPedersenCommitment<G>,
}

impl<G: AffineRepr> AuditorTxnProof<G> {
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<G>,
        eph_sk: G::ScalarField,
        eph_pk: G,
        auditor_sk: G::ScalarField,
        auditor_pk: G,
        accept: bool,
        nonce: &[u8],
        g: G,
    ) -> (Self, G::ScalarField) {
        let mut prover_transcript = MerlinTranscript::new(AUDITOR_TXN_LABEL);
        // Need to prove that auditor knows its secret key in the encryption of its public key

        // TODO: Should generator for ephemeral encryption key and account key be different?
        let t_enc_pk = PokPedersenCommitmentProtocol::init(
            eph_sk,
            G::ScalarField::rand(rng),
            &leg_enc.ct_a.eph_pk,
            auditor_sk,
            G::ScalarField::rand(rng),
            &g,
        );
        t_enc_pk
            .challenge_contribution(
                &leg_enc.ct_a.eph_pk,
                &g,
                &leg_enc.ct_a.encrypted,
                &mut prover_transcript,
            )
            .unwrap();

        // Hash the auditor's response
        if accept {
            prover_transcript
                .append_message(AUDITOR_TXN_RESPONSE_LABEL, AUDITOR_TXN_ACCEPT_RESPONSE);
        } else {
            prover_transcript
                .append_message(AUDITOR_TXN_RESPONSE_LABEL, AUDITOR_TXN_REJECT_RESPONSE);
        }

        let mut extra_instance = vec![];
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        eph_pk.serialize_compressed(&mut extra_instance).unwrap();
        auditor_pk
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();

        prover_transcript
            .append_message_without_static_label(AUDITOR_TXN_INSTANCE_LABEL, &extra_instance);

        let prover_challenge =
            prover_transcript.challenge_scalar::<G::ScalarField>(AUDITOR_TXN_CHALLENGE_LABEL);

        let resp_enc_pk = t_enc_pk.gen_proof(&prover_challenge);
        (Self { resp_enc_pk }, prover_challenge)
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G>,
        eph_pk: G,
        auditor_pk: G,
        accept: bool,
        prover_challenge: G::ScalarField,
        nonce: &[u8],
        g: G,
    ) -> Result<(), R1CSError> {
        let mut verifier_transcript = MerlinTranscript::new(AUDITOR_TXN_LABEL);

        self.resp_enc_pk
            .challenge_contribution(
                &leg_enc.ct_a.eph_pk,
                &g,
                &leg_enc.ct_a.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();

        // Verifier should also hash the auditor's response
        if accept {
            verifier_transcript
                .append_message(AUDITOR_TXN_RESPONSE_LABEL, AUDITOR_TXN_ACCEPT_RESPONSE);
        } else {
            verifier_transcript
                .append_message(AUDITOR_TXN_RESPONSE_LABEL, AUDITOR_TXN_REJECT_RESPONSE);
        }

        let mut extra_instance = vec![];
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        eph_pk.serialize_compressed(&mut extra_instance).unwrap();
        auditor_pk
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();

        verifier_transcript
            .append_message_without_static_label(AUDITOR_TXN_INSTANCE_LABEL, &extra_instance);

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<G::ScalarField>(AUDITOR_TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        assert!(self.resp_enc_pk.verify(
            &leg_enc.ct_a.encrypted,
            &leg_enc.ct_a.eph_pk,
            &g,
            &verifier_challenge
        ));
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::old::keys::{SigKey, VerKey, keygen_enc, keygen_sig};
    use ark_ec::CurveGroup;
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type PallasFr = ark_pallas::Fr;
    type VestaFr = ark_vesta::Fr;

    /// Generate account signing and encryption keys
    pub fn setup_keys<R: RngCore, G: AffineRepr>(
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
    fn leg_verification() {
        let mut rng = rand::thread_rng();
        // TODO: Find the optimum gen length for any circuit
        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        let auditor_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let leaf_comm_key = PallasA::rand(&mut rng);

        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;

        let leaf = create_leaf_for_auditor_tree(asset_id, pk_a.0, leaf_comm_key);

        let set = vec![leaf];
        let auditor_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &auditor_tree_params,
            Some(4),
        );

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
                (pk_a.0, pk_a_e.0),
                gen_p_1,
                gen_p_2,
            );

        // Venue gets the leaf path from the tree
        let path = auditor_tree.get_path_to_leaf_for_proof(0, 0);

        let (proof, prover_challenge) = SettlementTxnProof::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand,
            eph_sk_enc.clone(),
            pk_e.0,
            path,
            nonce,
            &auditor_tree_params,
            leaf_comm_key,
            gen_p_1,
            gen_p_2,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc.clone(),
                eph_sk_enc.clone(),
                pk_e.0,
                &auditor_tree,
                prover_challenge,
                nonce,
                &auditor_tree_params,
                leaf_comm_key,
                gen_p_1,
                gen_p_2,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );

        assert_eq!(
            eph_sk_enc.decrypt_for_sender::<Blake2b512>(sk_s_e.0),
            sk_e.0
        );
        assert_eq!(
            eph_sk_enc.decrypt_for_receiver::<Blake2b512>(sk_r_e.0),
            sk_e.0
        );
        assert_eq!(
            eph_sk_enc.decrypt_for_auditor::<Blake2b512>(sk_a_e.0),
            sk_e.0
        );

        assert_eq!(leg_enc.decrypt(&sk_e.0, gen_p_2), leg)
    }

    #[test]
    fn auditor_action() {
        let mut rng = rand::thread_rng();

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);

        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;
        let amount = 100;

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let (leg, leg_enc, leg_enc_rand, _, _, sk_e, pk_e) =
            initialize_leg_for_settlement::<_, _, Blake2b512>(
                &mut rng,
                asset_id,
                amount,
                (pk_s.0, pk_s_e.0),
                (pk_r.0, pk_r_e.0),
                (pk_a.0, pk_a_e.0),
                gen_p_1,
                gen_p_2,
            );

        let nonce = b"test-nonce";

        // Auditor "accept"ing in this case
        let accept = true;

        let clock = Instant::now();
        let (proof, prover_challenge) = AuditorTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            sk_e.0,
            pk_e.0,
            sk_a.0,
            pk_a.0,
            accept,
            nonce,
            gen_p_1,
        );
        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc.clone(),
                pk_e.0,
                pk_a.0,
                accept,
                prover_challenge,
                nonce,
                gen_p_1,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("proof size = {}", proof.compressed_size());
        println!(
            "prover time = {:?}, verifier time = {:?}",
            prover_time, verifier_time
        );
    }
}
