use crate::error::Result;
use crate::leg::leg_proof::ensure_leg_encryption_consistent;
use crate::leg::{Leg, LegEncryption, LegEncryptionRandomness};
use crate::util::bp_gens_for_vec_commitment;
use crate::{Error, LEG_ENC_LABEL, NONCE_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript};
use ark_ec::CurveGroup;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::marker::PhantomData;
use ark_std::string::ToString;
use ark_std::{format, vec, vec::Vec};
use bulletproofs::r1cs::{
    ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, VerificationTuple, Verifier,
    add_verification_tuple_to_rmc, verify_given_verification_tuple,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use dock_crypto_utils::transcript::Transcript;
use polymesh_dart_common::{BALANCE_BITS, Balance};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{PartialPokDiscreteLog, PartialPokPedersenCommitment};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;

pub const PUBLIC_ASSET_LEG_PROOF_TXN_LABEL: &[u8; 31] = b"public-asset-leg-creation-proof";

/// This leg creation proof is used when asset-id is revealed to the verifier so there is no curve
/// tree proof and the auditor and mediator public keys are also known to the verifier
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PublicAssetLegCreationProof<G: SWCurveConfig> {
    /// When this is None, external [`R1CSProof`] will be used and [`PublicAssetLegCreationProof`] only
    /// contains proof for the sigma protocols and enforces the Bulletproof constraints.
    pub r1cs_proof: Option<R1CSProof<Affine<G>>>,
    /// Commitment to randomness and response for proving knowledge of amount in twisted Elgamal encryption of amount.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_amount_enc: PartialPokPedersenCommitment<Affine<G>>,
    pub resp_ct_s: PartialPokPedersenCommitment<Affine<G>>,
    pub resp_ct_r: PartialPokPedersenCommitment<Affine<G>>,
    pub resp_eph_pk_s_v: PartialPokDiscreteLog<Affine<G>>,
    pub resp_eph_pk_r_v: PartialPokDiscreteLog<Affine<G>>,
    pub resp_eph_pk_s_r: Option<PartialPokDiscreteLog<Affine<G>>>,
    pub resp_eph_pk_r_s: Option<PartialPokDiscreteLog<Affine<G>>>,
    pub resp_ct_meds: Vec<PokDiscreteLog<Affine<G>>>,
    pub resp_eph_pk_meds: Vec<PartialPokDiscreteLog<Affine<G>>>,
    pub resp_ct_public_meds: Vec<PokDiscreteLog<Affine<G>>>,
    pub resp_eph_pk_public_meds: Vec<PartialPokDiscreteLog<Affine<G>>>,
    /// Proof of correctness of ephemeral public keys of asset auditors.
    pub resp_eph_pk_enc: Vec<(
        PartialPokDiscreteLog<Affine<G>>,
        PartialPokDiscreteLog<Affine<G>>,
        PartialPokDiscreteLog<Affine<G>>,
    )>,
    /// Proof of correctness of ephemeral public keys of public auditors.
    pub resp_eph_pk_public_enc: Vec<(
        PartialPokDiscreteLog<Affine<G>>,
        PartialPokDiscreteLog<Affine<G>>,
        PartialPokDiscreteLog<Affine<G>>,
    )>,
    /// Bulletproof vector commitment to `[amount, r_1, r_2, r_3, 1/r_1, 1/r_2, r_3/r_1, r_3/r_2]`.
    /// And this list might additionally have `r_2/r_1, r_1/r_2` as well if senders and receivers are allowed
    /// to see each other
    pub comm_r_i_amount: Affine<G>,
    pub t_comm_r_i_amount: Affine<G>,
    pub resp_comm_r_i_amount: SchnorrResponse<Affine<G>>,
}

impl<G: SWCurveConfig> PublicAssetLegCreationProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg: Leg<Affine<G>>,
        leg_enc: LegEncryption<Affine<G>>,
        leg_enc_rand: LegEncryptionRandomness<G::ScalarField>,
        nonce: &[u8],
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
        enc_key_gen: Affine<G>,
        enc_gen: Affine<G>,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
        let mut prover = Prover::new(&leaf_level_pc_gens, transcript);

        let mut proof = Self::new_with_given_prover(
            rng,
            leg,
            leg_enc,
            leg_enc_rand,
            nonce,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            enc_key_gen,
            enc_gen,
            &mut prover,
        )?;

        let r1cs_proof = prover.prove_with_rng(leaf_level_bp_gens, rng)?;
        proof.r1cs_proof = Some(r1cs_proof);

        Ok(proof)
    }

    pub fn new_with_given_prover<R: CryptoRngCore>(
        rng: &mut R,
        leg: Leg<Affine<G>>,
        leg_enc: LegEncryption<Affine<G>>,
        leg_enc_rand: LegEncryptionRandomness<G::ScalarField>,
        nonce: &[u8],
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
        enc_key_gen: Affine<G>,
        enc_gen: Affine<G>,
        prover: &mut Prover<MerlinTranscript, Affine<G>>,
    ) -> Result<Self> {
        {
            let transcript_ref = prover.transcript();
            add_to_transcript!(transcript_ref, NONCE_LABEL, nonce, LEG_ENC_LABEL, leg_enc,);
        }

        Self::new_with_given_prover_inner(
            rng,
            leg,
            leg_enc,
            leg_enc_rand,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            enc_key_gen,
            enc_gen,
            prover,
        )
    }

    pub(crate) fn new_with_given_prover_inner<R: CryptoRngCore>(
        rng: &mut R,
        leg: Leg<Affine<G>>,
        leg_enc: LegEncryption<Affine<G>>,
        leg_enc_rand: LegEncryptionRandomness<G::ScalarField>,
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
        enc_key_gen: Affine<G>,
        enc_gen: Affine<G>,
        prover: &mut Prover<MerlinTranscript, Affine<G>>,
    ) -> Result<Self> {
        if !leg_enc.is_asset_id_revealed() {
            return Err(Error::ProofGenerationError(
                "asset-id is hidden in leg encryption".to_string(),
            ));
        }

        ensure_leg_encryption_consistent(&leg, &leg_enc)?;

        let mut r_1 = leg_enc_rand.r1;
        let mut r_2 = leg_enc_rand.r2;
        let mut r_3 = leg_enc_rand.r3;

        let r_meds = leg_enc_rand.r_meds.clone();
        let r_public_meds = leg_enc_rand.r_public_meds.clone();

        let parties_see_each_other = leg_enc.do_parties_see_each_other();

        let mut r_1_inv = r_1.inverse().ok_or_else(|| Error::InvertingZero)?;
        let mut r_2_inv = r_2.inverse().ok_or_else(|| Error::InvertingZero)?;
        let mut r_3_r_1_inv = r_3 * r_1_inv;
        let mut r_3_r_2_inv = r_3 * r_2_inv;
        let r_2_r_1_inv = parties_see_each_other.then(|| r_2 * r_1_inv);
        let r_1_r_2_inv = parties_see_each_other.then(|| r_1 * r_2_inv);

        let mut amount_blinding = G::ScalarField::rand(rng);
        let mut r_1_blinding = G::ScalarField::rand(rng);
        let mut r_2_blinding = G::ScalarField::rand(rng);
        let mut r_3_blinding = G::ScalarField::rand(rng);
        let mut r_1_inv_blinding = G::ScalarField::rand(rng);
        let mut r_2_inv_blinding = G::ScalarField::rand(rng);
        let mut r_3_r_1_inv_blinding = G::ScalarField::rand(rng);
        let mut r_3_r_2_inv_blinding = G::ScalarField::rand(rng);
        let mut r_2_r_1_inv_blinding = parties_see_each_other.then(|| G::ScalarField::rand(rng));
        let mut r_1_r_2_inv_blinding = parties_see_each_other.then(|| G::ScalarField::rand(rng));

        let mut r_meds_blindings = (0..r_meds.len())
            .map(|_| G::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let mut r_public_meds_blindings = (0..r_public_meds.len())
            .map(|_| G::ScalarField::rand(rng))
            .collect::<Vec<_>>();

        let mut amount = G::ScalarField::from(leg.core.amount);

        // In the following comments, S and R are the ephemeral public keys of sender and receiver respectively
        // A and M refer to ephemeral public keys of auditor and mediator and depending on the context, they may
        // refer to asset's or the extra (always public) ones specified by the leg creator

        // For proving ct_s = enc_key_gen * r_1 + S[0] * r_1^{-1}
        let ct_s_proto = PokPedersenCommitmentProtocol::init(
            r_1,
            r_1_blinding,
            &enc_key_gen,
            r_1_inv,
            r_1_inv_blinding,
            &leg_enc.eph_pk_s.0,
        );

        // For proving ct_r = enc_key_gen * r_2 + R[1] * r_2^{-1}
        let ct_r_proto = PokPedersenCommitmentProtocol::init(
            r_2,
            r_2_blinding,
            &enc_key_gen,
            r_2_inv,
            r_2_inv_blinding,
            &leg_enc.eph_pk_r.1,
        );

        // For proving ct_amount = enc_key_gen * r_3 + enc_gen * amount
        let ct_amount_proto = PokPedersenCommitmentProtocol::init(
            r_3,
            r_3_blinding,
            &enc_key_gen,
            amount,
            amount_blinding,
            &enc_gen,
        );

        // For proving S[2] = S[0] * r_3/r_1
        let eph_pk_s_v_proto =
            PokDiscreteLogProtocol::init(r_3_r_1_inv, r_3_r_1_inv_blinding, &leg_enc.eph_pk_s.0);

        // For proving R[2] = R[1] * r_3/r_2
        let eph_pk_r_v_proto =
            PokDiscreteLogProtocol::init(r_3_r_2_inv, r_3_r_2_inv_blinding, &leg_enc.eph_pk_r.1);

        // If parties_see_each_other is true, then S[1] and R[0] is present in leg encryption
        // For proving S[1] = S[0] * r_2/r_1 and R[0] = R[1] * r_1/r_2
        let (eph_pk_s_r_proto, eph_pk_r_s_proto) = if parties_see_each_other {
            (
                Some(PokDiscreteLogProtocol::init(
                    r_2_r_1_inv.unwrap(),
                    r_2_r_1_inv_blinding.unwrap(),
                    &leg_enc.eph_pk_s.0,
                )),
                Some(PokDiscreteLogProtocol::init(
                    r_1_r_2_inv.unwrap(),
                    r_1_r_2_inv_blinding.unwrap(),
                    &leg_enc.eph_pk_r.1,
                )),
            )
        } else {
            (None, None)
        };

        let mut ct_meds_proto = Vec::with_capacity(leg_enc.ct_meds.len());
        let mut eph_pk_meds_proto = Vec::with_capacity(leg_enc.ct_meds.len());
        let mut eph_pk_enc_proto = Vec::with_capacity(leg_enc.eph_pk_enc_keys.len());
        let mut ct_public_meds_proto = Vec::with_capacity(leg_enc.ct_public_meds.len());
        let mut eph_pk_public_meds_proto = Vec::with_capacity(leg_enc.ct_public_meds.len());
        let mut eph_pk_public_enc_proto = Vec::with_capacity(leg_enc.eph_pk_public_enc_keys.len());

        for i in 0..leg_enc.ct_meds.len() {
            // For proving ct_m[i] - pk_m[i] = enc_key_gen * r_meds[i]
            ct_meds_proto.push(PokDiscreteLogProtocol::init(
                r_meds[i],
                r_meds_blindings[i],
                &enc_key_gen,
            ));
            // For proving M[i] = pk_en[i] * r_meds[i]
            eph_pk_meds_proto.push(PokDiscreteLogProtocol::init(
                r_meds[i],
                r_meds_blindings[i],
                &leg.enc_keys[leg.med_keys[i].0 as usize],
            ));
        }

        for i in 0..leg_enc.eph_pk_enc_keys.len() {
            // For proving
            // - A[i][0] = pk_en[i] * r_1
            // - A[i][1] = pk_en[i] * r_2
            // - A[i][2] = pk_en[i] * r_3
            eph_pk_enc_proto.push((
                PokDiscreteLogProtocol::init(r_1, r_1_blinding, &leg.enc_keys[i]),
                PokDiscreteLogProtocol::init(r_2, r_2_blinding, &leg.enc_keys[i]),
                PokDiscreteLogProtocol::init(r_3, r_3_blinding, &leg.enc_keys[i]),
            ));
        }

        for i in 0..leg_enc.ct_public_meds.len() {
            // For proving ct_m[i] - pk_m[i] = enc_key_gen * r_public_meds[i]
            ct_public_meds_proto.push(PokDiscreteLogProtocol::init(
                r_public_meds[i],
                r_public_meds_blindings[i],
                &enc_key_gen,
            ));
            // For proving M[i] = pk_en[i] * r_public_meds[i]
            eph_pk_public_meds_proto.push(PokDiscreteLogProtocol::init(
                r_public_meds[i],
                r_public_meds_blindings[i],
                &leg.public_enc_keys[leg.public_med_keys[i].0 as usize],
            ));
        }

        for i in 0..leg_enc.eph_pk_public_enc_keys.len() {
            // For proving
            // - A[i][0] = pk_en[i] * r_1
            // - A[i][1] = pk_en[i] * r_2
            // - A[i][2] = pk_en[i] * r_3
            eph_pk_public_enc_proto.push((
                PokDiscreteLogProtocol::init(r_1, r_1_blinding, &leg.public_enc_keys[i]),
                PokDiscreteLogProtocol::init(r_2, r_2_blinding, &leg.public_enc_keys[i]),
                PokDiscreteLogProtocol::init(r_3, r_3_blinding, &leg.public_enc_keys[i]),
            ));
        }

        let mut comm_r_i_blinding = G::ScalarField::rand(rng);
        let mut wits = vec![
            amount,
            r_1,
            r_2,
            r_3,
            r_1_inv,
            r_2_inv,
            r_3_r_1_inv,
            r_3_r_2_inv,
        ];
        // If S[1] and R[0] are present, then knowledge of r_2 / r_1 and r_1 / r_2 needs to be proven as well
        if parties_see_each_other {
            wits.push(r_2_r_1_inv.unwrap());
            wits.push(r_1_r_2_inv.unwrap());
        }

        // Commitment to `[amount, r_1, r_2, r_3, 1/r_1, 1/r_2, r_3/r_1, r_3/r_2]`. And this list might additionally
        // have `r_2/r_1, r_1/r_2` as well if senders and receivers are allowed to see each other
        let (comm_r_i_amount, vars) =
            prover.commit_vec(&wits, comm_r_i_blinding, leaf_level_bp_gens);

        Self::enforce_constraints(
            &mut *prover,
            Some(leg.core.amount),
            vars,
            parties_see_each_other,
        )?;

        // Sigma protocol for proving knowledge of `comm_r_i_amount`
        let mut blindings = vec![
            G::ScalarField::rand(rng),
            amount_blinding,
            r_1_blinding,
            r_2_blinding,
            r_3_blinding,
            r_1_inv_blinding,
            r_2_inv_blinding,
            r_3_r_1_inv_blinding,
            r_3_r_2_inv_blinding,
        ];
        if parties_see_each_other {
            blindings.push(r_2_r_1_inv_blinding.unwrap());
            blindings.push(r_1_r_2_inv_blinding.unwrap());
        }
        let t_comm_r_i_amount = SchnorrCommitment::new(
            &Self::bp_gens(
                parties_see_each_other,
                leaf_level_pc_gens,
                leaf_level_bp_gens,
            ),
            blindings,
        );

        Zeroize::zeroize(&mut amount);
        Zeroize::zeroize(&mut r_1);
        Zeroize::zeroize(&mut r_2);
        Zeroize::zeroize(&mut r_3);
        Zeroize::zeroize(&mut r_1_inv);
        Zeroize::zeroize(&mut r_2_inv);
        Zeroize::zeroize(&mut r_3_r_1_inv);
        Zeroize::zeroize(&mut r_3_r_2_inv);
        Zeroize::zeroize(&mut amount_blinding);
        Zeroize::zeroize(&mut r_1_blinding);
        Zeroize::zeroize(&mut r_2_blinding);
        Zeroize::zeroize(&mut r_3_blinding);
        Zeroize::zeroize(&mut r_1_inv_blinding);
        Zeroize::zeroize(&mut r_2_inv_blinding);
        Zeroize::zeroize(&mut r_3_r_1_inv_blinding);
        Zeroize::zeroize(&mut r_3_r_2_inv_blinding);
        Zeroize::zeroize(&mut r_2_r_1_inv_blinding);
        Zeroize::zeroize(&mut r_1_r_2_inv_blinding);

        Zeroize::zeroize(&mut r_meds_blindings);
        Zeroize::zeroize(&mut r_public_meds_blindings);

        {
            let mut transcript_ref = prover.transcript();

            ct_s_proto.challenge_contribution(
                &enc_key_gen,
                &leg_enc.eph_pk_s.0,
                &leg_enc.ct_s,
                &mut transcript_ref,
            )?;

            ct_r_proto.challenge_contribution(
                &enc_key_gen,
                &leg_enc.eph_pk_r.1,
                &leg_enc.ct_r,
                &mut transcript_ref,
            )?;

            ct_amount_proto.challenge_contribution(
                &enc_key_gen,
                &enc_gen,
                &leg_enc.ct_amount,
                &mut transcript_ref,
            )?;

            eph_pk_s_v_proto.challenge_contribution(
                &leg_enc.eph_pk_s.0,
                &leg_enc.eph_pk_s.2,
                &mut transcript_ref,
            )?;

            eph_pk_r_v_proto.challenge_contribution(
                &leg_enc.eph_pk_r.1,
                &leg_enc.eph_pk_r.2,
                &mut transcript_ref,
            )?;

            if let Some(p) = &eph_pk_s_r_proto {
                p.challenge_contribution(
                    &leg_enc.eph_pk_s.0,
                    &leg_enc.eph_pk_s.1.unwrap(),
                    &mut transcript_ref,
                )?;
            }

            if let Some(p) = &eph_pk_r_s_proto {
                p.challenge_contribution(
                    &leg_enc.eph_pk_r.1,
                    &leg_enc.eph_pk_r.0.unwrap(),
                    &mut transcript_ref,
                )?;
            }

            let y_ct_meds = (0..leg_enc.ct_meds.len())
                .map(|i| leg_enc.ct_meds[i] - leg.med_keys[i].1)
                .collect::<Vec<_>>();
            let y_ct_meds = Projective::normalize_batch(&y_ct_meds);
            for i in 0..leg_enc.ct_meds.len() {
                ct_meds_proto[i].challenge_contribution(
                    &enc_key_gen,
                    &y_ct_meds[i],
                    &mut transcript_ref,
                )?;
                eph_pk_meds_proto[i].challenge_contribution(
                    &leg.enc_keys[leg.med_keys[i].0 as usize],
                    &leg_enc.eph_pk_med_keys[i].1,
                    &mut transcript_ref,
                )?;
            }

            for i in 0..leg_enc.eph_pk_enc_keys.len() {
                eph_pk_enc_proto[i].0.challenge_contribution(
                    &leg.enc_keys[i],
                    &leg_enc.eph_pk_enc_keys[i].0,
                    &mut transcript_ref,
                )?;
                eph_pk_enc_proto[i].1.challenge_contribution(
                    &leg.enc_keys[i],
                    &leg_enc.eph_pk_enc_keys[i].1,
                    &mut transcript_ref,
                )?;
                eph_pk_enc_proto[i].2.challenge_contribution(
                    &leg.enc_keys[i],
                    &leg_enc.eph_pk_enc_keys[i].2,
                    &mut transcript_ref,
                )?;
            }

            let y_ct_public_meds = (0..leg_enc.ct_public_meds.len())
                .map(|i| leg_enc.ct_public_meds[i] - leg.public_med_keys[i].1)
                .collect::<Vec<_>>();
            let y_ct_public_meds = Projective::normalize_batch(&y_ct_public_meds);
            for i in 0..leg_enc.ct_public_meds.len() {
                ct_public_meds_proto[i].challenge_contribution(
                    &enc_key_gen,
                    &y_ct_public_meds[i],
                    &mut transcript_ref,
                )?;
                eph_pk_public_meds_proto[i].challenge_contribution(
                    &leg.public_enc_keys[leg.public_med_keys[i].0 as usize],
                    &leg_enc.eph_pk_public_med_keys[i].1,
                    &mut transcript_ref,
                )?;
            }

            for i in 0..leg_enc.eph_pk_public_enc_keys.len() {
                eph_pk_public_enc_proto[i].0.challenge_contribution(
                    &leg.public_enc_keys[i],
                    &leg_enc.eph_pk_public_enc_keys[i].0,
                    &mut transcript_ref,
                )?;
                eph_pk_public_enc_proto[i].1.challenge_contribution(
                    &leg.public_enc_keys[i],
                    &leg_enc.eph_pk_public_enc_keys[i].1,
                    &mut transcript_ref,
                )?;
                eph_pk_public_enc_proto[i].2.challenge_contribution(
                    &leg.public_enc_keys[i],
                    &leg_enc.eph_pk_public_enc_keys[i].2,
                    &mut transcript_ref,
                )?;
            }

            t_comm_r_i_amount.challenge_contribution(&mut transcript_ref)?;
        }

        let challenge = prover
            .transcript()
            .challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        // Responses for various r_i and its variations and amount are present in response for t_comm_r_i_amount
        let resp_ct_s = ct_s_proto.gen_partial_proof();
        let resp_ct_r = ct_r_proto.gen_partial_proof();
        let resp_ct_amount = ct_amount_proto.gen_partial_proof();
        let resp_eph_pk_s_v = eph_pk_s_v_proto.gen_partial_proof();
        let resp_eph_pk_r_v = eph_pk_r_v_proto.gen_partial_proof();

        let resp_eph_pk_s_r = eph_pk_s_r_proto.map(|p| p.gen_partial_proof());
        let resp_eph_pk_r_s = eph_pk_r_s_proto.map(|p| p.gen_partial_proof());

        let resp_ct_meds = ct_meds_proto
            .into_iter()
            .map(|p| p.gen_proof(&challenge))
            .collect();
        let resp_eph_pk_meds = eph_pk_meds_proto
            .into_iter()
            .map(|p| p.gen_partial_proof())
            .collect();
        let resp_ct_public_meds = ct_public_meds_proto
            .into_iter()
            .map(|p| p.gen_proof(&challenge))
            .collect();
        let resp_eph_pk_public_meds = eph_pk_public_meds_proto
            .into_iter()
            .map(|p| p.gen_partial_proof())
            .collect();

        let resp_eph_pk_enc = eph_pk_enc_proto
            .into_iter()
            .map(|(p0, p1, p2)| {
                (
                    p0.gen_partial_proof(),
                    p1.gen_partial_proof(),
                    p2.gen_partial_proof(),
                )
            })
            .collect();
        let resp_eph_pk_public_enc = eph_pk_public_enc_proto
            .into_iter()
            .map(|(p0, p1, p2)| {
                (
                    p0.gen_partial_proof(),
                    p1.gen_partial_proof(),
                    p2.gen_partial_proof(),
                )
            })
            .collect();

        // For this commitment, the witness will extra blinding from BP
        wits.insert(0, comm_r_i_blinding);
        let resp_comm_r_i_amount = t_comm_r_i_amount.response(&wits, &challenge)?;

        Zeroize::zeroize(&mut comm_r_i_blinding);
        Zeroize::zeroize(&mut wits);
        Ok(Self {
            r1cs_proof: None,
            resp_amount_enc: resp_ct_amount,
            resp_ct_s,
            resp_ct_r,
            resp_eph_pk_s_v,
            resp_eph_pk_r_v,
            resp_eph_pk_s_r,
            resp_eph_pk_r_s,
            resp_ct_meds,
            resp_eph_pk_meds,
            resp_ct_public_meds,
            resp_eph_pk_public_meds,
            resp_eph_pk_enc,
            resp_eph_pk_public_enc,
            comm_r_i_amount,
            t_comm_r_i_amount: t_comm_r_i_amount.t,
            resp_comm_r_i_amount,
        })
    }

    /// Verifier will know the asset-id and thus know the encryption (auditor) and mediator keys.
    /// `enc_keys` and `med_keys` are the encryption (auditor) and mediator keys associated with the asset
    /// and become known to the verifier since the asset-id is known.
    /// `public_enc_keys` and `public_med_keys` are the extra encryption (auditor) and mediator keys
    /// specified by leg creator and are always known to the verifier
    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G>>,
        enc_keys: Vec<Affine<G>>,
        med_keys: Vec<(u8, Affine<G>)>, // (index in enc_keys, mediator affirmation key)
        public_enc_keys: Vec<Affine<G>>,
        public_med_keys: Vec<(u8, Affine<G>)>, // (index in public_enc_keys, mediator affirmation key)
        nonce: &[u8],
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
        enc_key_gen: Affine<G>,
        enc_gen: Affine<G>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
    ) -> Result<()> {
        let tuple = self.verify_and_return_tuples(
            leg_enc,
            enc_keys,
            med_keys,
            public_enc_keys,
            public_med_keys,
            nonce,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            enc_key_gen,
            enc_gen,
            rng,
            rmc.as_deref_mut(),
        )?;

        match rmc.as_mut() {
            Some(rmc) => {
                add_verification_tuple_to_rmc(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens, rmc)
                    .map_err(|e| e.into())
            }
            _ => verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens)
                .map_err(|e| e.into()),
        }
    }

    /// `enc_keys` and `med_keys` are the encryption (auditor) and mediator keys associated with the asset
    /// and become known to the verifier since the asset-id is known.
    /// `public_enc_keys` and `public_med_keys` are the extra encryption (auditor) and mediator keys
    /// specified by leg creator and are always known to the verifier
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G>>,
        enc_keys: Vec<Affine<G>>,
        med_keys: Vec<(u8, Affine<G>)>, // (index in enc_keys, mediator affirmation key)
        public_enc_keys: Vec<Affine<G>>,
        public_med_keys: Vec<(u8, Affine<G>)>, // (index in public_enc_keys, mediator affirmation key)
        nonce: &[u8],
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
        enc_key_gen: Affine<G>,
        enc_gen: Affine<G>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
    ) -> Result<VerificationTuple<Affine<G>>> {
        let verifier_transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);
        self.verify_sigma_protocols_and_enforce_constraints(
            leg_enc,
            enc_keys,
            med_keys,
            public_enc_keys,
            public_med_keys,
            nonce,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            enc_key_gen,
            enc_gen,
            &mut verifier,
            rmc,
        )?;

        let proof = self
            .r1cs_proof
            .as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof is missing".to_string()))?;
        let tuple = verifier.verification_scalars_and_points_with_rng(proof, rng)?;
        Ok(tuple)
    }

    /// `enc_keys` and `med_keys` are the encryption (auditor) and mediator keys associated with the asset
    /// and become known to the verifier since the asset-id is known.
    /// `public_enc_keys` and `public_med_keys` are the extra encryption (auditor) and mediator keys
    /// specified by leg creator and are always known to the verifier
    pub fn verify_sigma_protocols_and_enforce_constraints(
        &self,
        leg_enc: LegEncryption<Affine<G>>,
        enc_keys: Vec<Affine<G>>,
        med_keys: Vec<(u8, Affine<G>)>, // (index in enc_keys, mediator affirmation key)
        public_enc_keys: Vec<Affine<G>>,
        public_med_keys: Vec<(u8, Affine<G>)>, // (index in public_enc_keys, mediator affirmation key)
        nonce: &[u8],
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
        enc_key_gen: Affine<G>,
        enc_gen: Affine<G>,
        verifier: &mut Verifier<MerlinTranscript, Affine<G>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
    ) -> Result<()> {
        {
            add_to_transcript!(
                verifier.transcript(),
                NONCE_LABEL,
                nonce,
                LEG_ENC_LABEL,
                leg_enc,
            );
        }

        self.verify_sigma_protocols_and_enforce_constraints_inner(
            leg_enc,
            enc_keys,
            med_keys,
            public_enc_keys,
            public_med_keys,
            leaf_level_pc_gens,
            leaf_level_bp_gens,
            enc_key_gen,
            enc_gen,
            verifier,
            rmc,
        )
    }

    pub(crate) fn verify_sigma_protocols_and_enforce_constraints_inner(
        &self,
        leg_enc: LegEncryption<Affine<G>>,
        enc_keys: Vec<Affine<G>>,
        med_keys: Vec<(u8, Affine<G>)>, // (index in enc_keys, mediator affirmation key)
        public_enc_keys: Vec<Affine<G>>,
        public_med_keys: Vec<(u8, Affine<G>)>, // (index in public_enc_keys, mediator affirmation key)
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
        enc_key_gen: Affine<G>,
        enc_gen: Affine<G>,
        verifier: &mut Verifier<MerlinTranscript, Affine<G>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
    ) -> Result<()> {
        if !leg_enc.is_asset_id_revealed() {
            return Err(Error::ProofVerificationError(
                "asset-id is hidden in leg encryption".to_string(),
            ));
        }

        if self.resp_eph_pk_enc.len() != enc_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_eph_pk_enc.len() != enc_keys.len() ({} != {})",
                self.resp_eph_pk_enc.len(),
                enc_keys.len()
            )));
        }
        if self.resp_ct_meds.len() != med_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_ct_meds.len() != enc_keys.len() ({} != {})",
                self.resp_ct_meds.len(),
                med_keys.len()
            )));
        }
        if self.resp_eph_pk_meds.len() != med_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_eph_pk_meds.len() != enc_keys.len() ({} != {})",
                self.resp_eph_pk_meds.len(),
                med_keys.len()
            )));
        }

        if self.resp_eph_pk_public_enc.len() != public_enc_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_eph_pk_public_enc.len() != public_enc_keys.len() ({} != {})",
                self.resp_eph_pk_public_enc.len(),
                public_enc_keys.len()
            )));
        }
        if self.resp_ct_public_meds.len() != public_med_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_ct_public_meds.len() != public_med_keys.len() ({} != {})",
                self.resp_ct_public_meds.len(),
                public_med_keys.len()
            )));
        }
        if self.resp_eph_pk_public_meds.len() != public_med_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_eph_pk_public_meds.len() != public_med_keys.len() ({} != {})",
                self.resp_eph_pk_public_meds.len(),
                public_med_keys.len()
            )));
        }

        let parties_see_each_other = leg_enc.do_parties_see_each_other();

        let vars = verifier.commit_vec(
            8 + if parties_see_each_other { 2 } else { 0 },
            self.comm_r_i_amount,
        );
        Self::enforce_constraints(&mut *verifier, None, vars, parties_see_each_other)?;

        let mut transcript_ref = verifier.transcript();

        self.resp_ct_s.challenge_contribution(
            &enc_key_gen,
            &leg_enc.eph_pk_s.0,
            &leg_enc.ct_s,
            &mut transcript_ref,
        )?;

        self.resp_ct_r.challenge_contribution(
            &enc_key_gen,
            &leg_enc.eph_pk_r.1,
            &leg_enc.ct_r,
            &mut transcript_ref,
        )?;

        self.resp_amount_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_amount,
            &mut transcript_ref,
        )?;

        self.resp_eph_pk_s_v.challenge_contribution(
            &leg_enc.eph_pk_s.0,
            &leg_enc.eph_pk_s.2,
            &mut transcript_ref,
        )?;

        self.resp_eph_pk_r_v.challenge_contribution(
            &leg_enc.eph_pk_r.1,
            &leg_enc.eph_pk_r.2,
            &mut transcript_ref,
        )?;

        if let Some(resp) = &self.resp_eph_pk_s_r {
            resp.challenge_contribution(
                &leg_enc.eph_pk_s.0,
                &leg_enc.eph_pk_s.1.unwrap(),
                &mut transcript_ref,
            )?;
        }

        if let Some(resp) = &self.resp_eph_pk_r_s {
            resp.challenge_contribution(
                &leg_enc.eph_pk_r.1,
                &leg_enc.eph_pk_r.0.unwrap(),
                &mut transcript_ref,
            )?;
        }

        let y_ct_meds = (0..leg_enc.ct_meds.len())
            .map(|i| leg_enc.ct_meds[i] - med_keys[i].1)
            .collect::<Vec<_>>();
        let y_ct_meds = Projective::normalize_batch(&y_ct_meds);

        let y_ct_public_meds = (0..leg_enc.ct_public_meds.len())
            .map(|i| leg_enc.ct_public_meds[i] - public_med_keys[i].1)
            .collect::<Vec<_>>();
        let y_ct_public_meds = Projective::normalize_batch(&y_ct_public_meds);

        for i in 0..self.resp_ct_meds.len() {
            self.resp_ct_meds[i].challenge_contribution(
                &enc_key_gen,
                &y_ct_meds[i],
                &mut transcript_ref,
            )?;
            // M[i] = pk_en[med_keys[i].0] * r_meds[i]
            self.resp_eph_pk_meds[i].challenge_contribution(
                &enc_keys[med_keys[i].0 as usize],
                &leg_enc.eph_pk_med_keys[i].1,
                &mut transcript_ref,
            )?;
        }

        // A[i][0] = pk_en[i] * r_1, A[i][1] = pk_en[i] * r_2, A[i][2] = pk_en[i] * r_3
        for i in 0..self.resp_eph_pk_enc.len() {
            self.resp_eph_pk_enc[i].0.challenge_contribution(
                &enc_keys[i],
                &leg_enc.eph_pk_enc_keys[i].0,
                &mut transcript_ref,
            )?;
            self.resp_eph_pk_enc[i].1.challenge_contribution(
                &enc_keys[i],
                &leg_enc.eph_pk_enc_keys[i].1,
                &mut transcript_ref,
            )?;
            self.resp_eph_pk_enc[i].2.challenge_contribution(
                &enc_keys[i],
                &leg_enc.eph_pk_enc_keys[i].2,
                &mut transcript_ref,
            )?;
        }

        for i in 0..self.resp_ct_public_meds.len() {
            self.resp_ct_public_meds[i].challenge_contribution(
                &enc_key_gen,
                &y_ct_public_meds[i],
                &mut transcript_ref,
            )?;
            // M[i] = pk_en[public_med_keys[i].0] * r_public_meds[i]
            self.resp_eph_pk_public_meds[i].challenge_contribution(
                &public_enc_keys[public_med_keys[i].0 as usize],
                &leg_enc.eph_pk_public_med_keys[i].1,
                &mut transcript_ref,
            )?;
        }

        // A[i][0] = pk_en[i] * r_1, A[i][1] = pk_en[i] * r_2, A[i][2] = pk_en[i] * r_3
        for i in 0..self.resp_eph_pk_public_enc.len() {
            self.resp_eph_pk_public_enc[i].0.challenge_contribution(
                &public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].0,
                &mut transcript_ref,
            )?;
            self.resp_eph_pk_public_enc[i].1.challenge_contribution(
                &public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].1,
                &mut transcript_ref,
            )?;
            self.resp_eph_pk_public_enc[i].2.challenge_contribution(
                &public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].2,
                &mut transcript_ref,
            )?;
        }

        self.t_comm_r_i_amount
            .serialize_compressed(&mut transcript_ref)?;

        let challenge = transcript_ref.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        // Verify ct_s = enc_key_gen * r_1 + S[0] * r_1^{-1}
        verify_or_rmc_3!(
            rmc,
            self.resp_ct_s,
            "resp_ct_s verification failed",
            leg_enc.ct_s,
            enc_key_gen,
            leg_enc.eph_pk_s.0,
            &challenge,
            &self.resp_comm_r_i_amount.0[2],
            &self.resp_comm_r_i_amount.0[5],
        );

        // Verify ct_r = enc_key_gen * r_2 + R[1] * r_2^{-1}
        verify_or_rmc_3!(
            rmc,
            self.resp_ct_r,
            "resp_ct_r verification failed",
            leg_enc.ct_r,
            enc_key_gen,
            leg_enc.eph_pk_r.1,
            &challenge,
            &self.resp_comm_r_i_amount.0[3],
            &self.resp_comm_r_i_amount.0[6],
        );

        // Verify ct_amount = enc_key_gen * r_3 + enc_gen * amount
        verify_or_rmc_3!(
            rmc,
            self.resp_amount_enc,
            "resp_amount_enc verification failed",
            leg_enc.ct_amount,
            enc_key_gen,
            enc_gen,
            &challenge,
            &self.resp_comm_r_i_amount.0[4],
            &self.resp_comm_r_i_amount.0[1],
        );

        // Verify S[2] = S[0] * r_3/r_1
        verify_or_rmc_2!(
            rmc,
            self.resp_eph_pk_s_v,
            "resp_eph_pk_s_v verification failed",
            leg_enc.eph_pk_s.2,
            leg_enc.eph_pk_s.0,
            &challenge,
            &self.resp_comm_r_i_amount.0[7],
        );

        // Verify R[2] = R[1] * r_3/r_2
        verify_or_rmc_2!(
            rmc,
            self.resp_eph_pk_r_v,
            "resp_eph_pk_r_v verification failed",
            leg_enc.eph_pk_r.2,
            leg_enc.eph_pk_r.1,
            &challenge,
            &self.resp_comm_r_i_amount.0[8],
        );

        if parties_see_each_other {
            // Verify S[1] = S[0] * r_2/r_1
            if let Some(resp) = &self.resp_eph_pk_s_r {
                verify_or_rmc_2!(
                    rmc,
                    resp,
                    "resp_eph_pk_s_r verification failed",
                    leg_enc.eph_pk_s.1.unwrap(),
                    leg_enc.eph_pk_s.0,
                    &challenge,
                    &self.resp_comm_r_i_amount.0[9],
                );
            }

            // Verify R[0] = R[1] * r_1/r_2
            if let Some(resp) = &self.resp_eph_pk_r_s {
                verify_or_rmc_2!(
                    rmc,
                    resp,
                    "resp_eph_pk_r_s verification failed",
                    leg_enc.eph_pk_r.0.unwrap(),
                    leg_enc.eph_pk_r.1,
                    &challenge,
                    &self.resp_comm_r_i_amount.0[10],
                );
            }
        }

        // Verify mediator ciphertexts and ephemeral keys
        for i in 0..self.resp_ct_meds.len() {
            verify_or_rmc_2!(
                rmc,
                self.resp_ct_meds[i],
                format!("resp_ct_meds[{}] verification failed", i),
                y_ct_meds[i],
                enc_key_gen,
                &challenge,
            );

            // M[i] = pk_en[med_keys[i].0] * r_meds[i]
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_meds[i],
                format!("resp_eph_pk_meds[{}] verification failed", i),
                leg_enc.eph_pk_med_keys[i].1,
                enc_keys[med_keys[i].0 as usize],
                &challenge,
                &self.resp_ct_meds[i].response,
            );
        }

        // Verify ephemeral keys for encryption keys: A[i][0] = pk_en[i] * r_1, A[i][1] = pk_en[i] * r_2, A[i][2] = pk_en[i] * r_3
        for i in 0..self.resp_eph_pk_enc.len() {
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_enc[i].0,
                format!("resp_eph_pk_enc[{}].0 verification failed", i),
                leg_enc.eph_pk_enc_keys[i].0,
                enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[2],
            );
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_enc[i].1,
                format!("resp_eph_pk_enc[{}].1 verification failed", i),
                leg_enc.eph_pk_enc_keys[i].1,
                enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[3],
            );
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_enc[i].2,
                format!("resp_eph_pk_enc[{}].2 verification failed", i),
                leg_enc.eph_pk_enc_keys[i].2,
                enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[4],
            );
        }

        // Verify public mediator ciphertexts and ephemeral keys
        for i in 0..self.resp_ct_public_meds.len() {
            verify_or_rmc_2!(
                rmc,
                self.resp_ct_public_meds[i],
                format!("resp_ct_public_meds[{}] verification failed", i),
                y_ct_public_meds[i],
                enc_key_gen,
                &challenge,
            );

            // M[i] = pk_en[public_med_keys[i].0] * r_public_meds[i]
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_public_meds[i],
                format!("resp_eph_pk_public_meds[{}] verification failed", i),
                leg_enc.eph_pk_public_med_keys[i].1,
                public_enc_keys[public_med_keys[i].0 as usize],
                &challenge,
                &self.resp_ct_public_meds[i].response,
            );
        }

        // Verify public ephemeral keys for encryption keys: A[i][0] = pk_en[i] * r_1, A[i][1] = pk_en[i] * r_2, A[i][2] = pk_en[i] * r_3
        for i in 0..self.resp_eph_pk_public_enc.len() {
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_public_enc[i].0,
                format!("resp_eph_pk_public_enc[{}].0 verification failed", i),
                leg_enc.eph_pk_public_enc_keys[i].0,
                public_enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[2],
            );
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_public_enc[i].1,
                format!("resp_eph_pk_public_enc[{}].1 verification failed", i),
                leg_enc.eph_pk_public_enc_keys[i].1,
                public_enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[3],
            );
            verify_or_rmc_2!(
                rmc,
                self.resp_eph_pk_public_enc[i].2,
                format!("resp_eph_pk_public_enc[{}].2 verification failed", i),
                leg_enc.eph_pk_public_enc_keys[i].2,
                public_enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[4],
            );
        }

        // Verify the commitment to r_i and amount
        verify_schnorr_resp_or_rmc!(
            rmc,
            self.resp_comm_r_i_amount,
            Self::bp_gens(
                parties_see_each_other,
                leaf_level_pc_gens,
                leaf_level_bp_gens,
            ),
            self.comm_r_i_amount,
            self.t_comm_r_i_amount,
            &challenge,
        );

        Ok(())
    }

    fn enforce_constraints<CS: ConstraintSystem<G::ScalarField>>(
        cs: &mut CS,
        amount: Option<Balance>,
        mut committed_variables: Vec<Variable<G::ScalarField>>,
        parties_see_each_other: bool,
    ) -> Result<()> {
        let (var_r1_r2_inv, var_r2_r1_inv) = if parties_see_each_other {
            (
                Some(committed_variables.pop().unwrap()),
                Some(committed_variables.pop().unwrap()),
            )
        } else {
            (None, None)
        };

        let var_r3_r2_inv = committed_variables.pop().unwrap();
        let var_r3_r1_inv = committed_variables.pop().unwrap();
        let var_r2_inv = committed_variables.pop().unwrap();
        let var_r1_inv = committed_variables.pop().unwrap();
        let var_r3 = committed_variables.pop().unwrap();
        let var_r2 = committed_variables.pop().unwrap();
        let var_r1 = committed_variables.pop().unwrap();
        let var_amount = committed_variables.pop().unwrap();

        let lc_one = LinearCombination::from(Variable::One(PhantomData));

        // r_1 * 1/r_1 = 1
        let lc_r1 = LinearCombination::from(var_r1);
        let lc_r1_inv = LinearCombination::from(var_r1_inv);
        let (_, _, one) = cs.multiply(lc_r1.clone(), lc_r1_inv.clone());
        cs.constrain(one - lc_one.clone());

        // r_2 * 1/r_2 = 1
        let lc_r2 = LinearCombination::from(var_r2);
        let lc_r2_inv = LinearCombination::from(var_r2_inv);
        let (_, _, one) = cs.multiply(lc_r2.clone(), lc_r2_inv.clone());
        cs.constrain(one - lc_one);

        let lc_r3 = LinearCombination::from(var_r3);

        // r_1 * r_3/r_1 = r_3
        let (_, _, r3) = cs.multiply(lc_r1.clone(), var_r3_r1_inv.into());
        cs.constrain(lc_r3.clone() - r3);

        // r_2 * r_3/r_2 = r_3
        let (_, _, r3) = cs.multiply(lc_r2.clone(), var_r3_r2_inv.into());
        cs.constrain(lc_r3.clone() - r3);

        if parties_see_each_other {
            // r_1 * r_2/r_1 = r_2
            let (_, _, r2) = cs.multiply(lc_r1.clone(), var_r2_r1_inv.unwrap().into());
            cs.constrain(lc_r2.clone() - r2);

            // r_2 * r_1/r_2 = r_1
            let (_, _, r1) = cs.multiply(lc_r2, var_r1_r2_inv.unwrap().into());
            cs.constrain(lc_r1 - r1);
        }

        // TODO: What if we do range proof outside circuit? Or using another protocol like Bulletproofs++?
        range_proof(
            cs,
            var_amount.into(),
            amount.map(|a| a as u128),
            BALANCE_BITS.into(),
        )?;
        Ok(())
    }

    fn bp_gens(
        parties_see_each_other: bool,
        leaf_level_pc_gens: &PedersenGens<Affine<G>>,
        leaf_level_bp_gens: &BulletproofGens<Affine<G>>,
    ) -> Vec<Affine<G>> {
        let mut gens = vec![leaf_level_pc_gens.B_blinding];
        for g in bp_gens_for_vec_commitment(
            8 + if parties_see_each_other { 2 } else { 0 },
            leaf_level_bp_gens,
        ) {
            gens.push(g);
        }
        gens
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::leg::{Leg, LegEncConfig};
    use ark_pallas::PallasConfig;
    use ark_serialize::CanonicalSerialize;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use std::time::Instant;

    type Fr = ark_pallas::Fr;

    #[test]
    fn public_asset_leg_proof() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;

        let label = b"test";
        let sig_key_gen = hash_to_pallas(label, b"sig-key-g").into();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into();

        let leaf_level_pc_gens = PedersenGens::<Affine<PallasConfig>>::default();
        let leaf_level_bp_gens = BulletproofGens::<Affine<PallasConfig>>::new(NUM_GENS as u32, 1);

        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let num_enc_keys = 2;
        let num_mediators = 2;
        let num_public_enc_keys = 1;
        let num_public_mediators = 1;

        let keys_enc = (0..num_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();
        let keys_public_enc = (0..num_public_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_public_mediator = (0..num_public_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let amount = 100;
        let asset_id = 1;
        let nonce = b"test-nonce";

        let enc_keys: Vec<_> = keys_enc.iter().map(|(_, k)| k.0).collect();
        let med_keys: Vec<_> = keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_enc_keys as u8, k.0))
            .collect();
        let public_enc_keys: Vec<_> = keys_public_enc.iter().map(|(_, k)| k.0).collect();
        let public_med_keys: Vec<_> = keys_public_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_public_enc_keys as u8, k.0))
            .collect();

        let leg = Leg::new(
            pk_s_e.0,
            pk_r_e.0,
            amount,
            asset_id,
            enc_keys.clone(),
            med_keys.clone(),
            public_enc_keys.clone(),
            public_med_keys.clone(),
        )
        .unwrap();

        let (leg_enc, leg_enc_rand) = leg
            .encrypt(
                &mut rng,
                LegEncConfig {
                    parties_see_each_other: true,
                    reveal_asset_id: true,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        assert!(leg_enc.is_asset_id_revealed());
        assert_eq!(leg_enc.asset_id(), Some(asset_id));

        // Test with parties_see_each_other = true
        let clock = Instant::now();
        let proof = PublicAssetLegCreationProof::<PallasConfig>::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand,
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();
        let prover_time = clock.elapsed();

        let proof_size = proof.compressed_size();

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                enc_keys.clone(),
                med_keys.clone(),
                public_enc_keys.clone(),
                public_med_keys.clone(),
                nonce,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifier_time = clock.elapsed();

        let clock = Instant::now();
        let mut rmc = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                enc_keys.clone(),
                med_keys.clone(),
                public_enc_keys.clone(),
                public_med_keys.clone(),
                nonce,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                enc_key_gen,
                enc_gen,
                Some(&mut rmc),
            )
            .unwrap();
        assert!(rmc.verify());
        let verifier_time_rmc = clock.elapsed();

        println!("For public asset leg proof (parties_see_each_other = true)");
        println!("total proof size = {}", proof_size);
        println!("total prover time = {:?}", prover_time);
        println!("verifier time (regular) = {:?}", verifier_time);
        println!("verifier time (RMC) = {:?}", verifier_time_rmc);

        // sender and receiver can't learn each other's public key
        let (leg_enc, leg_enc_rand) = leg
            .encrypt(
                &mut rng,
                LegEncConfig {
                    parties_see_each_other: false,
                    reveal_asset_id: true,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        assert!(leg_enc.is_asset_id_revealed());
        assert_eq!(leg_enc.asset_id(), Some(asset_id));

        let clock = Instant::now();
        let proof = PublicAssetLegCreationProof::<PallasConfig>::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand,
            nonce,
            &leaf_level_pc_gens,
            &leaf_level_bp_gens,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();
        let prover_time = clock.elapsed();

        let proof_size = proof.compressed_size();

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                enc_keys.clone(),
                med_keys.clone(),
                public_enc_keys.clone(),
                public_med_keys.clone(),
                nonce,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifier_time = clock.elapsed();

        let clock = Instant::now();
        let mut rmc = RandomizedMultChecker::new(ark_pallas::Fr::rand(&mut rng));
        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                enc_keys.clone(),
                med_keys.clone(),
                public_enc_keys.clone(),
                public_med_keys.clone(),
                nonce,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                enc_key_gen,
                enc_gen,
                Some(&mut rmc),
            )
            .unwrap();
        assert!(rmc.verify());
        let verifier_time_rmc = clock.elapsed();

        println!("For public asset leg proof (parties_see_each_other = false)");
        println!("total proof size = {}", proof_size);
        println!("total prover time = {:?}", prover_time);
        println!("verifier time (regular) = {:?}", verifier_time);
        println!("verifier time (RMC) = {:?}", verifier_time_rmc);
    }

    #[test]
    fn batch_public_asset_leg_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const BATCH_SIZE: usize = 5;

        let label = b"test";
        let sig_key_gen = hash_to_pallas(label, b"sig-key-g").into();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into();

        let leaf_level_pc_gens = PedersenGens::<Affine<PallasConfig>>::default();
        let leaf_level_bp_gens = BulletproofGens::<Affine<PallasConfig>>::new(NUM_GENS as u32, 1);

        // Setup common encryption and mediator keys
        let num_enc_keys = 3;
        let num_mediators = 2;
        let num_public_enc_keys = 2;
        let num_public_mediators = 1;

        let keys_enc = (0..num_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();
        let keys_public_enc = (0..num_public_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_public_mediator = (0..num_public_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let enc_keys: Vec<_> = keys_enc.iter().map(|(_, k)| k.0).collect();
        let med_keys: Vec<_> = keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_enc_keys as u8, k.0))
            .collect();
        let public_enc_keys: Vec<_> = keys_public_enc.iter().map(|(_, k)| k.0).collect();
        let public_med_keys: Vec<_> = keys_public_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_public_enc_keys as u8, k.0))
            .collect();

        // Create multiple legs and proofs
        let mut legs = Vec::new();
        let mut leg_encs = Vec::new();
        let mut proofs = Vec::new();
        let mut nonces = Vec::new();

        let proving_clock = Instant::now();
        for i in 0..BATCH_SIZE {
            let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
            let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

            let amount = 100 * (i as u64 + 1);
            let asset_id = i as u32 + 1;
            let nonce = format!("batch-nonce-{}", i).into_bytes();

            let leg = Leg::new(
                pk_s_e.0,
                pk_r_e.0,
                amount,
                asset_id,
                enc_keys.clone(),
                med_keys.clone(),
                public_enc_keys.clone(),
                public_med_keys.clone(),
            )
            .unwrap();

            let (leg_enc, leg_enc_rand) = leg
                .encrypt(
                    &mut rng,
                    LegEncConfig {
                        parties_see_each_other: i % 2 == 0,
                        reveal_asset_id: true,
                    },
                    enc_key_gen,
                    enc_gen,
                )
                .unwrap();

            let proof = PublicAssetLegCreationProof::<PallasConfig>::new(
                &mut rng,
                leg.clone(),
                leg_enc.clone(),
                leg_enc_rand,
                &nonce,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            legs.push(leg);
            leg_encs.push(leg_enc);
            proofs.push(proof);
            nonces.push(nonce);
        }
        let total_proving_time = proving_clock.elapsed();

        let total_proof_size: usize = proofs.iter().map(|p| p.compressed_size()).sum();

        let individual_verify_clock = Instant::now();
        for i in 0..BATCH_SIZE {
            proofs[i]
                .verify(
                    &mut rng,
                    leg_encs[i].clone(),
                    enc_keys.clone(),
                    med_keys.clone(),
                    public_enc_keys.clone(),
                    public_med_keys.clone(),
                    &nonces[i],
                    &leaf_level_pc_gens,
                    &leaf_level_bp_gens,
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        }
        let individual_verify_time = individual_verify_clock.elapsed();

        let rmc_verify_clock = Instant::now();
        let mut rmc = RandomizedMultChecker::new(Fr::rand(&mut rng));
        let mut tuples = Vec::new();

        // Collect verification tuples (can be done in parallel)
        for i in 0..BATCH_SIZE {
            let tuple = proofs[i]
                .verify_and_return_tuples(
                    leg_encs[i].clone(),
                    enc_keys.clone(),
                    med_keys.clone(),
                    public_enc_keys.clone(),
                    public_med_keys.clone(),
                    &nonces[i],
                    &leaf_level_pc_gens,
                    &leaf_level_bp_gens,
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    Some(&mut rmc),
                )
                .unwrap();
            tuples.push(tuple);
        }

        for tuple in tuples {
            add_verification_tuple_to_rmc(
                tuple,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                &mut rmc,
            )
            .unwrap();
        }

        assert!(rmc.verify());
        let rmc_verify_time = rmc_verify_clock.elapsed();

        println!(
            "For {} public asset leg proofs, total proof size = {}",
            BATCH_SIZE, total_proof_size
        );
        println!("total prover time = {:?}", total_proving_time);
        println!("verifier time (individual) = {:?}", individual_verify_time);
        println!("verifier time (with RMC) = {:?}", rmc_verify_time);
    }

    #[test]
    fn combined_public_asset_leg_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const BATCH_SIZE: usize = 3;

        let label = b"test";
        let sig_key_gen = hash_to_pallas(label, b"sig-key-g").into();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into();

        let leaf_level_pc_gens = PedersenGens::<Affine<PallasConfig>>::default();
        let leaf_level_bp_gens = BulletproofGens::<Affine<PallasConfig>>::new(NUM_GENS as u32, 1);

        let asset_id = 1;
        let nonce = b"combined-nonce";

        // Setup common encryption and mediator keys
        let num_enc_keys = 3;
        let num_mediators = 2;
        let num_public_enc_keys = 2;
        let num_public_mediators = 1;

        let keys_enc = (0..num_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();
        let keys_public_enc = (0..num_public_enc_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_public_mediator = (0..num_public_mediators)
            .map(|_| keygen_sig(&mut rng, sig_key_gen))
            .collect::<Vec<_>>();

        let enc_keys: Vec<_> = keys_enc.iter().map(|(_, k)| k.0).collect();
        let med_keys: Vec<_> = keys_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_enc_keys as u8, k.0))
            .collect();
        let public_enc_keys: Vec<_> = keys_public_enc.iter().map(|(_, k)| k.0).collect();
        let public_med_keys: Vec<_> = keys_public_mediator
            .iter()
            .enumerate()
            .map(|(i, (_, k))| (i as u8 % num_public_enc_keys as u8, k.0))
            .collect();

        let mut legs = Vec::with_capacity(BATCH_SIZE);
        let mut leg_encs = Vec::with_capacity(BATCH_SIZE);
        let mut leg_enc_rands = Vec::with_capacity(BATCH_SIZE);

        for i in 0..BATCH_SIZE {
            let amount = 1000;

            let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
            let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

            let leg = Leg::new(
                pk_s_e.0,
                pk_r_e.0,
                amount,
                asset_id,
                enc_keys.clone(),
                med_keys.clone(),
                public_enc_keys.clone(),
                public_med_keys.clone(),
            )
            .unwrap();

            let (leg_enc, leg_enc_rand) = leg
                .encrypt(
                    &mut rng,
                    LegEncConfig {
                        parties_see_each_other: i % 2 == 0,
                        reveal_asset_id: true,
                    },
                    enc_key_gen,
                    enc_gen,
                )
                .unwrap();

            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
        }

        let combined_prove_clock = Instant::now();
        let transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
        let mut prover = Prover::new(&leaf_level_pc_gens, transcript);

        let mut proofs = Vec::with_capacity(BATCH_SIZE);
        for i in 0..BATCH_SIZE {
            let proof = PublicAssetLegCreationProof::<PallasConfig>::new_with_given_prover(
                &mut rng,
                legs[i].clone(),
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                nonce,
                &leaf_level_pc_gens,
                &leaf_level_bp_gens,
                enc_key_gen,
                enc_gen,
                &mut prover,
            )
            .unwrap();
            proofs.push(proof);
        }

        let r1cs_proof = prover
            .prove_with_rng(&leaf_level_bp_gens, &mut rng)
            .unwrap();
        for proof in &mut proofs {
            proof.r1cs_proof = Some(r1cs_proof.clone());
        }
        let combined_prove_time = combined_prove_clock.elapsed();

        let total_proof_size: usize = proofs.iter().map(|p| p.compressed_size()).sum();

        let combined_verify_clock = Instant::now();
        let verifier_transcript = MerlinTranscript::new(PUBLIC_ASSET_LEG_PROOF_TXN_LABEL);
        let mut verifier = Verifier::new(verifier_transcript);

        for i in 0..BATCH_SIZE {
            proofs[i]
                .verify_sigma_protocols_and_enforce_constraints(
                    leg_encs[i].clone(),
                    enc_keys.clone(),
                    med_keys.clone(),
                    public_enc_keys.clone(),
                    public_med_keys.clone(),
                    nonce,
                    &leaf_level_pc_gens,
                    &leaf_level_bp_gens,
                    enc_key_gen,
                    enc_gen,
                    &mut verifier,
                    None,
                )
                .unwrap();
        }

        let tuple = verifier
            .verification_scalars_and_points_with_rng(&r1cs_proof, &mut rng)
            .unwrap();

        verify_given_verification_tuple(tuple, &leaf_level_pc_gens, &leaf_level_bp_gens).unwrap();

        let combined_verify_time = combined_verify_clock.elapsed();

        println!(
            "For {} public asset leg proofs (combined), total proof size = {}",
            BATCH_SIZE, total_proof_size
        );
        println!("total prover time (combined) = {:?}", combined_prove_time);
        println!("verifier time (combined) = {:?}", combined_verify_time);
    }
}
