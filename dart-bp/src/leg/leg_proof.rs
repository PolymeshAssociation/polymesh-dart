use crate::leg::{
    AssetCommitmentParams, AssetData, LEG_TXN_CHALLENGE_LABEL, LEG_TXN_EVEN_LABEL,
    LEG_TXN_ODD_LABEL, Leg, LegEncryption, LegEncryptionRandomness,
};
use crate::util::{
    BPProof, bp_gens_for_vec_commitment, get_verification_tuples_with_rng,
    handle_verification_tuples, prove_with_rng,
};
use crate::{
    Error, LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, add_to_transcript,
    error::Result,
};
use ark_dlog_gadget::dlog::{DiscreteLogParameters, DivisorComms};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::marker::PhantomData;
use ark_std::string::ToString;
use ark_std::{collections::BTreeSet, format, vec, vec::Vec};
use bulletproofs::r1cs::{
    ConstraintSystem, LinearCombination, Prover, Variable, VerificationTuple, Verifier,
};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use curve_tree_relations::ped_comm_group_elems::{
    ReRandomizedPoints, prove as prove_ped_com, verify as verify_ped_com,
};
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{BALANCE_BITS, Balance};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;

/// This is the proof for a single leg creation. Report section 5.1.5
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegCreationProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// When this is None, external [`R1CSProof`] will be used and [`LegCreationProof`] only
    /// contains proof for the sigma protocols and enforces the Bulletproof constraints.
    pub r1cs_proof: Option<BPProof<G1, G0>>,
    /// When using batched proving,
    /// this will be None as the path is computed externally.
    /// For non-batched proving, this contains the full re-randomized path.
    pub re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G1, G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in twisted Elgamal encryption of amount.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_amount_enc: PartialPokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving asset-id in twisted Elgamal encryption of asset-id.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_asset_id_enc: PartialPokPedersenCommitment<Affine<G0>>,
    pub resp_asset_id: PokPedersenCommitment<Affine<G0>>,
    pub re_randomized_points: ReRandomizedPoints<G0>,
    /// Bulletproof vector commitment to the following list
    /// `[amount, r_1, r_2, r_3, r_4, 1/r_1, 1/r_2, r_2/r_1, r_3/r_1, r_3/r_2, r_4/r_1, r_4/r_2] || [r_2/r_1, r_1/r_2] || [l_0, l_0 * r_1, l_1, l_1 * r_1, ...,] || [m_0, m_0 / r_1, m_1, m_1 / r_1, ....]`
    /// present only when sender and receiver decryption is needed.
    /// The third list is when asset has any encryption keys and fourth list when asset has mediators
    pub comm_r_i_amount: Affine<G0>,
    pub t_comm_r_i_amount: Affine<G0>,
    pub resp_comm_r_i_amount: SchnorrResponse<Affine<G0>>,
    pub ped_comms: Vec<DivisorComms<Affine<G1>>>,
    /// Response for proving ct_s = enc_key_gen * r_1 + S[0] * r_1^{-1}
    pub resp_ct_s: PartialPokPedersenCommitment<Affine<G0>>,
    /// Response for proving ct_r = enc_key_gen * r_2 + R[1] * r_2^{-1}
    pub resp_ct_r: PartialPokPedersenCommitment<Affine<G0>>,
    /// Response for proving S[2] = S[0] * r_3/r_1
    pub resp_eph_pk_s_v: PartialPokDiscreteLog<Affine<G0>>,
    /// Response for proving S[3] = S[0] * r_4/r_1
    pub resp_eph_pk_s_at: PartialPokDiscreteLog<Affine<G0>>,
    /// Response for proving R[2] = R[1] * r_3/r_2
    pub resp_eph_pk_r_v: PartialPokDiscreteLog<Affine<G0>>,
    /// Response for proving R[3] = R[1] * r_4/r_2
    pub resp_eph_pk_r_at: PartialPokDiscreteLog<Affine<G0>>,
    /// Responses for proving encryption key relations
    pub resp_eph_pk_enc: Vec<(
        PartialPokPedersenCommitment<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
    )>,
    /// Responses for proving mediator key relations
    pub resp_eph_pk_meds: Vec<(
        Partial2PokPedersenCommitment<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
    )>,
    /// Response for proving S[1] = S[0] * r_2/r_1 (only when sender_receiver_decryption_needed)
    pub resp_eph_pk_s_r: Option<PartialPokDiscreteLog<Affine<G0>>>,
    /// Response for proving R[0] = R[1] * r_1/r_2 (only when sender_receiver_decryption_needed)
    pub resp_eph_pk_r_s: Option<PartialPokDiscreteLog<Affine<G0>>>,
    /// Responses for proving public encryption key relations
    pub resp_eph_pk_public_enc: Vec<(
        PartialPokDiscreteLog<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
        PartialPokDiscreteLog<Affine<G0>>,
    )>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> LegCreationProof<L, F0, F1, G0, G1>
{
    /// Creates a new proof using the new curve tree protocol with divisor commitments
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        leaf_path: CurveTreeWitnessPath<L, G1, G0>,
        asset_data: AssetData<F0, F1, G0, G1>,
        asset_tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &tree_parameters.even_parameters.sl_params.pc_gens(),
            even_transcript,
        );
        let mut odd_prover = Prover::new(
            &tree_parameters.odd_parameters.sl_params.pc_gens(),
            odd_transcript,
        );

        let mut proof = Self::new_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            leg,
            leg_enc,
            leg_enc_rand,
            leaf_path,
            asset_data,
            asset_tree_root,
            nonce,
            tree_parameters,
            asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )?;

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &tree_parameters.even_parameters.bp_gens(),
            &tree_parameters.odd_parameters.bp_gens(),
            rng,
        )?;
        proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });
        Ok(proof)
    }

    pub fn new_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        leaf_path: CurveTreeWitnessPath<L, G1, G0>,
        asset_data: AssetData<F0, F1, G0, G1>,
        asset_tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    ) -> Result<Self> {
        let (re_randomized_path, re_randomization_of_leaf) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<_, Parameters1, Parameters0>(
                even_prover,
                odd_prover,
                tree_parameters,
                rng,
            )?;

        add_to_transcript!(
            odd_prover.transcript(),
            ROOT_LABEL,
            asset_tree_root,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path
        );

        add_to_transcript!(odd_prover.transcript(), LEG_ENC_LABEL, leg_enc,);

        let rerandomized_leaf = re_randomized_path.path.get_rerandomized_leaf();

        Self::new_with_given_prover_inner::<_, Parameters0, Parameters1>(
            rng,
            leg,
            leg_enc,
            leg_enc_rand,
            rerandomized_leaf,
            re_randomization_of_leaf,
            asset_data,
            tree_parameters,
            asset_comm_params,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
            Some(re_randomized_path),
        )
    }

    pub(crate) fn new_with_given_prover_inner<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        leg: Leg<Affine<G0>>,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        rerandomized_leaf: Affine<G1>,
        mut re_randomization_of_leaf: F1,
        asset_data: AssetData<F0, F1, G0, G1>,
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G1, G0>>,
    ) -> Result<Self> {
        if leg_enc.is_asset_id_revealed() {
            return Err(Error::ProofGenerationError(
                "asset-id is revealed in leg encryption".to_string(),
            ));
        }

        ensure_leg_encryption_consistent(&leg, &leg_enc)?;

        let mut at = F0::from(leg.core.asset_id);
        let mut amount = F0::from(leg.core.amount);

        let num_asset_data_keys = asset_data.num_total_keys();

        let asset_data_points = AssetData::points(
            leg.core.asset_id,
            &asset_data.enc_keys,
            &asset_data.med_keys,
            &asset_comm_params,
        );

        let num_asset_data_points = asset_data_points.len();

        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if cfg!(debug_assertions) {
            let x_coords = asset_data_points
                .clone()
                .into_iter()
                .map(|p| {
                    (tree_parameters.odd_parameters.sl_params.delta + p)
                        .into_affine()
                        .x
                })
                .collect::<Vec<_>>();
            let commitment = Projective::<G1>::msm(
                &asset_comm_params.comm_key[..num_asset_data_points],
                x_coords.as_slice(),
            )
            .unwrap();
            assert_eq!(
                commitment
                    + (tree_parameters.even_parameters.pc_gens().B_blinding
                        * re_randomization_of_leaf),
                rerandomized_leaf.into_group()
            );
        }

        let mut blindings_for_points = (0..num_asset_data_points)
            .map(|_| F0::rand(rng))
            .collect::<Vec<_>>();

        let num_enc_keys = asset_data.num_encryption_keys();
        let num_med_keys = asset_data.num_mediator_keys();

        let mut key_indices = BTreeSet::new();
        for i in 0..(num_enc_keys + num_med_keys) {
            key_indices.insert(i + 1);
        }
        let (re_randomized_points, ped_comms) = prove_ped_com::<_, _, _, _, G0, Parameters1>(
            rng,
            even_prover,
            asset_data_points,
            &rerandomized_leaf,
            re_randomization_of_leaf,
            blindings_for_points.clone(),
            &tree_parameters.odd_parameters,
            &tree_parameters.even_parameters.bp_gens(),
            key_indices,
        )?;

        Zeroize::zeroize(&mut re_randomization_of_leaf);

        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if cfg!(debug_assertions) {
            assert_eq!(
                re_randomized_points.re_randomized_points[0].into_group(),
                (asset_comm_params.j_0 * at)
                    + (tree_parameters.odd_parameters.pc_gens().B_blinding
                        * blindings_for_points[0])
            );

            for i in 0..num_asset_data_keys {
                let k = if i < num_enc_keys {
                    asset_data.enc_keys[i]
                } else {
                    (asset_comm_params.j_0
                        + asset_comm_params.j_1 * F0::from(asset_data.med_keys[i - num_enc_keys].0)
                        + asset_data.med_keys[i - num_enc_keys].1)
                        .into_affine()
                };
                assert_eq!(
                    re_randomized_points.re_randomized_points[i + 1].into_group(),
                    k + (tree_parameters.odd_parameters.pc_gens().B_blinding
                        * blindings_for_points[i + 1])
                );

                assert_eq!(
                    re_randomized_points.blindings_with_different_gen[&(i + 1)].into_group(),
                    tree_parameters.odd_parameters.pc_gens().B * blindings_for_points[i + 1]
                );
            }
        }

        let mut r_1 = leg_enc_rand.r1;
        let mut r_2 = leg_enc_rand.r2;
        let mut r_3 = leg_enc_rand.r3;
        let mut r_4 = leg_enc_rand.r4.unwrap();

        // Randomness used in mediator ciphertext, `ct_{m,i} = enc_key_gen * m_i + pk_m` and `M_i = pk_{e, j} * m_i`
        let r_meds = leg_enc_rand.r_meds.clone();

        let parties_see_each_other = leg_enc.do_parties_see_each_other();

        // Blindings used for encryption (auditor) keys, `pk_{{e,i}_r} = pk_{e,i} * l_i`. Skip first point since its for asset-id
        let l = blindings_for_points
            .iter()
            .skip(1)
            .take(num_enc_keys)
            .map(|k| *k)
            .collect::<Vec<_>>();

        // Blindings used for mediator keys, `pk_{{m,i}_r} = pk_{m,i} * k_i`. Skip first point since its for asset-id and then points for encryption keys
        let k = blindings_for_points
            .iter()
            .skip(1 + num_enc_keys)
            .take(num_med_keys)
            .map(|k| *k)
            .collect::<Vec<_>>();

        debug_assert_eq!(l.len() + k.len() + 1, num_asset_data_points);

        // If ct_s and ct_r need to be decrypted.
        let sender_receiver_decryption_needed = parties_see_each_other || !l.is_empty();

        let mut r_1_inv = r_1.inverse().ok_or_else(|| Error::InvertingZero)?;
        let mut r_2_inv = r_2.inverse().ok_or_else(|| Error::InvertingZero)?;
        // r_3/r_1
        let mut r_3_r_1_inv = r_3 * r_1_inv;
        // r_3/r_2
        let mut r_3_r_2_inv = r_3 * r_2_inv;
        // r_4/r_1
        let mut r_4_r_1_inv = r_4 * r_1_inv;
        // r_4/r_2
        let mut r_4_r_2_inv = r_4 * r_2_inv;
        // r_2/r_1
        let mut r_2_r_1_inv = sender_receiver_decryption_needed.then(|| r_2 * r_1_inv);
        // r_1/r_2
        let mut r_1_r_2_inv = sender_receiver_decryption_needed.then(|| r_1 * r_2_inv);

        // `l_i * r_1`
        let l_r_1 = l.iter().map(|l_i| *l_i * r_1).collect::<Vec<_>>();

        // `m_i * 1/r_1`
        let m_r_1_inv = r_meds.iter().map(|m_i| *m_i * r_1_inv).collect::<Vec<_>>();

        let mut amount_blinding = F0::rand(rng);
        let mut r_1_blinding = F0::rand(rng);
        let mut r_2_blinding = F0::rand(rng);
        let mut r_3_blinding = F0::rand(rng);
        let mut r_4_blinding = F0::rand(rng);
        let mut r_1_inv_blinding = F0::rand(rng);
        let mut r_2_inv_blinding = F0::rand(rng);
        let mut r_3_r_1_inv_blinding = F0::rand(rng);
        let mut r_3_r_2_inv_blinding = F0::rand(rng);
        let mut r_4_r_1_inv_blinding = F0::rand(rng);
        let mut r_4_r_2_inv_blinding = F0::rand(rng);
        let mut r_2_r_1_inv_blinding = sender_receiver_decryption_needed.then(|| F0::rand(rng));
        let mut r_1_r_2_inv_blinding = sender_receiver_decryption_needed.then(|| F0::rand(rng));
        let mut l_blindings = (0..l.len()).map(|_| F0::rand(rng)).collect::<Vec<_>>();
        let mut l_r_1_blindings = (0..l.len()).map(|_| F0::rand(rng)).collect::<Vec<_>>();
        let mut m_blindings = (0..r_meds.len()).map(|_| F0::rand(rng)).collect::<Vec<_>>();
        let mut m_r_1_inv_blindings = (0..r_meds.len()).map(|_| F0::rand(rng)).collect::<Vec<_>>();
        let mut k_blindings = (0..k.len()).map(|_| F0::rand(rng)).collect::<Vec<_>>();

        let mut asset_id_blinding = F0::rand(rng);

        let mut comm_r_i_blinding = F0::rand(rng);
        let mut wits = vec![
            amount,
            r_1,
            r_2,
            r_3,
            r_4,
            r_1_inv,
            r_2_inv,
            r_3_r_1_inv,
            r_3_r_2_inv,
            r_4_r_1_inv,
            r_4_r_2_inv,
        ];

        if sender_receiver_decryption_needed {
            wits.push(r_2_r_1_inv.unwrap());
            wits.push(r_1_r_2_inv.unwrap());
        }

        for (l_i, l_i_r_1) in l.iter().zip(l_r_1.iter()) {
            wits.push(*l_i);
            wits.push(*l_i_r_1);
        }
        for (m_i, m_i_r_1_inv) in r_meds.iter().zip(m_r_1_inv.iter()) {
            wits.push(*m_i);
            wits.push(*m_i_r_1_inv);
        }

        let (comm_r_i_amount, vars) = odd_prover.commit_vec(
            &wits,
            comm_r_i_blinding,
            &tree_parameters.odd_parameters.bp_gens(),
        );
        LegCreationProof::<L, F0, F1, G0, G1>::enforce_constraints(
            odd_prover,
            Some(leg.core.amount),
            sender_receiver_decryption_needed,
            l.len(),
            r_meds.len(),
            vars,
        )?;

        // Sigma protocol for proving knowledge of `comm_r_i_amount`
        let mut blindings = vec![
            F0::rand(rng),
            amount_blinding,
            r_1_blinding,
            r_2_blinding,
            r_3_blinding,
            r_4_blinding,
            r_1_inv_blinding,
            r_2_inv_blinding,
            r_3_r_1_inv_blinding,
            r_3_r_2_inv_blinding,
            r_4_r_1_inv_blinding,
            r_4_r_2_inv_blinding,
        ];
        if sender_receiver_decryption_needed {
            blindings.push(r_2_r_1_inv_blinding.unwrap());
            blindings.push(r_1_r_2_inv_blinding.unwrap());
        }
        for (l_i, l_i_r_1) in l_blindings.iter().zip(l_r_1_blindings.iter()) {
            blindings.push(*l_i);
            blindings.push(*l_i_r_1);
        }
        for (m_i, m_i_r_1_inv) in m_blindings.iter().zip(m_r_1_inv_blindings.iter()) {
            blindings.push(*m_i);
            blindings.push(*m_i_r_1_inv);
        }

        let t_comm_r_i_amount = SchnorrCommitment::new(
            &Self::bp_gens_vec::<Parameters0, Parameters1>(
                sender_receiver_decryption_needed,
                l.len(),
                r_meds.len(),
                tree_parameters,
            ),
            blindings,
        );

        let mut transcript = odd_prover.transcript();

        // In the following comments, S and R are the ephemeral public keys of sender and receiver respectively

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

        // For proving ct_asset_id = enc_key_gen * r_4 + enc_gen * asset_id
        let ct_asset_id_proto = PokPedersenCommitmentProtocol::init(
            r_4,
            r_4_blinding,
            &enc_key_gen,
            at,
            asset_id_blinding,
            &enc_gen,
        );

        // For proving S[2] = S[0] * r_3/r_1
        let eph_pk_s_v_proto =
            PokDiscreteLogProtocol::init(r_3_r_1_inv, r_3_r_1_inv_blinding, &leg_enc.eph_pk_s.0);

        // For proving S[3] = S[0] * r_4/r_1
        let eph_pk_s_at_proto =
            PokDiscreteLogProtocol::init(r_4_r_1_inv, r_4_r_1_inv_blinding, &leg_enc.eph_pk_s.0);

        // For proving R[2] = R[1] * r_3/r_2
        let eph_pk_r_v_proto =
            PokDiscreteLogProtocol::init(r_3_r_2_inv, r_3_r_2_inv_blinding, &leg_enc.eph_pk_r.1);

        // For proving R[3] = R[1] * r_4/r_2
        let eph_pk_r_at_proto =
            PokDiscreteLogProtocol::init(r_4_r_2_inv, r_4_r_2_inv_blinding, &leg_enc.eph_pk_r.1);

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

        let blinding_base = -tree_parameters
            .odd_parameters
            .pc_gens()
            .B_blinding
            .into_group()
            .into_affine();
        let b_base = tree_parameters.odd_parameters.pc_gens().B;

        let mut pk_en_proto = Vec::with_capacity(l.len());
        for i in 0..l.len() {
            // Since role=0 for encryption keys, no effect on base and thus its re_randomized_points[i + 1].0
            // For proving relation `A_i[0] = pk_{{en,i}_r} * r_1 + blinding_base * l_i * r_1`
            let t_1 = PokPedersenCommitmentProtocol::init(
                r_1,
                r_1_blinding,
                &re_randomized_points.re_randomized_points[i + 1],
                l_r_1[i],
                l_r_1_blindings[i],
                &blinding_base,
            );

            debug_assert_eq!(
                re_randomized_points.blindings_with_different_gen[&(i + 1)].into_group(),
                b_base * l[i]
            );

            // For proving relation `re_randomized_points[i + 1].1 = B * l_i`
            let t_1_1 = PokDiscreteLogProtocol::init(l[i], l_blindings[i], &b_base);

            let base = &leg_enc.eph_pk_enc_keys[i].0;
            // unwrap is fine since its created in this proof and guaranteed to be not None if l is non-empty

            // For proving relation `A_i[1] = A_i[0] * r_2/r_1`
            let t_2 = PokDiscreteLogProtocol::init(
                r_2_r_1_inv.unwrap(),
                r_2_r_1_inv_blinding.unwrap(),
                base,
            );
            // For proving relation `A_i[2] = A_i[0] * r_3/r_1`
            let t_3 = PokDiscreteLogProtocol::init(r_3_r_1_inv, r_3_r_1_inv_blinding, base);
            // For proving relation `A_i[3] = A_i[0] * r_4/r_1`
            let t_4 = PokDiscreteLogProtocol::init(r_4_r_1_inv, r_4_r_1_inv_blinding, base);

            pk_en_proto.push((t_1, t_1_1, t_2, t_3, t_4));
        }

        let mut pk_m_proto = Vec::with_capacity(r_meds.len());
        for i in 0..r_meds.len() {
            // role=1 for mediator keys
            // For proving relation `ct_m[i] + j_0 + j_1 * index - pk_{{m,i}_r} = enc_key_gen * r_meds[i] + blinding_base * k[i]`
            let t_m = PokPedersenCommitmentProtocol::init(
                r_meds[i],
                m_blindings[i],
                &enc_key_gen,
                k[i],
                k_blindings[i],
                &blinding_base,
            );

            debug_assert_eq!(
                re_randomized_points.blindings_with_different_gen[&(1 + num_enc_keys + i)]
                    .into_group(),
                b_base * k[i]
            );

            // For proving relation `re_randomized_points[1 + num_enc_keys + i].1 = B * k_i`
            let t_k = PokDiscreteLogProtocol::init(k[i], k_blindings[i], &b_base);

            let base = &leg_enc.eph_pk_enc_keys[leg_enc.eph_pk_med_keys[i].0 as usize].0;

            // For proving relation `M_i[0] = A_j[0] * r_meds[i] / r_1`
            let t_eph_m = PokDiscreteLogProtocol::init(m_r_1_inv[i], m_r_1_inv_blindings[i], base);
            pk_m_proto.push((t_m, t_k, t_eph_m));
        }

        let mut eph_pk_public_enc_proto = Vec::with_capacity(leg.public_enc_keys.len());
        for i in 0..leg.public_enc_keys.len() {
            // For proving A[i][0] = pk_en[i] * r_1, A[i][1] = pk_en[i] * r_2, A[i][2] = pk_en[i] * r_3
            eph_pk_public_enc_proto.push((
                PokDiscreteLogProtocol::init(r_1, r_1_blinding, &leg.public_enc_keys[i]),
                PokDiscreteLogProtocol::init(r_2, r_2_blinding, &leg.public_enc_keys[i]),
                PokDiscreteLogProtocol::init(r_3, r_3_blinding, &leg.public_enc_keys[i]),
            ));
        }

        // Proving correctness of asset-id in the point
        let t_asset_id = PokPedersenCommitmentProtocol::init(
            at,
            asset_id_blinding,
            &asset_comm_params.j_0,
            blindings_for_points[0],
            F0::rand(rng),
            &tree_parameters.odd_parameters.pc_gens().B_blinding,
        );

        Zeroize::zeroize(&mut r_1_blinding);
        Zeroize::zeroize(&mut r_2_blinding);
        Zeroize::zeroize(&mut r_1_inv_blinding);
        Zeroize::zeroize(&mut r_2_inv_blinding);
        Zeroize::zeroize(&mut r_2_r_1_inv_blinding);
        Zeroize::zeroize(&mut r_3_r_1_inv_blinding);
        Zeroize::zeroize(&mut r_3_r_2_inv_blinding);
        Zeroize::zeroize(&mut r_4_r_1_inv_blinding);
        Zeroize::zeroize(&mut r_4_r_2_inv_blinding);
        Zeroize::zeroize(&mut r_1_r_2_inv_blinding);

        Zeroize::zeroize(&mut r_3_blinding);
        Zeroize::zeroize(&mut amount_blinding);
        Zeroize::zeroize(&mut r_4_blinding);

        Zeroize::zeroize(&mut asset_id_blinding);
        Zeroize::zeroize(&mut at);
        Zeroize::zeroize(&mut blindings_for_points);

        Zeroize::zeroize(&mut l_blindings);
        Zeroize::zeroize(&mut l_r_1_blindings);
        Zeroize::zeroize(&mut m_blindings);
        Zeroize::zeroize(&mut m_r_1_inv_blindings);
        Zeroize::zeroize(&mut k_blindings);

        t_comm_r_i_amount.challenge_contribution(&mut transcript)?;

        ct_s_proto.challenge_contribution(
            &enc_key_gen,
            &leg_enc.eph_pk_s.0,
            &leg_enc.ct_s,
            &mut transcript,
        )?;

        ct_r_proto.challenge_contribution(
            &enc_key_gen,
            &leg_enc.eph_pk_r.1,
            &leg_enc.ct_r,
            &mut transcript,
        )?;

        ct_amount_proto.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_amount,
            &mut transcript,
        )?;

        ct_asset_id_proto.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.asset_id_ciphertext().unwrap(),
            &mut transcript,
        )?;

        eph_pk_s_v_proto.challenge_contribution(
            &leg_enc.eph_pk_s.0,
            &leg_enc.eph_pk_s.2,
            &mut transcript,
        )?;

        eph_pk_s_at_proto.challenge_contribution(
            &leg_enc.eph_pk_s.0,
            leg_enc.eph_pk_s.3.as_ref().unwrap(),
            &mut transcript,
        )?;

        eph_pk_r_v_proto.challenge_contribution(
            &leg_enc.eph_pk_r.1,
            &leg_enc.eph_pk_r.2,
            &mut transcript,
        )?;

        eph_pk_r_at_proto.challenge_contribution(
            &leg_enc.eph_pk_r.1,
            leg_enc.eph_pk_r.3.as_ref().unwrap(),
            &mut transcript,
        )?;

        if parties_see_each_other {
            eph_pk_s_r_proto.as_ref().unwrap().challenge_contribution(
                &leg_enc.eph_pk_s.0,
                leg_enc.eph_pk_s.1.as_ref().unwrap(),
                &mut transcript,
            )?;
            eph_pk_r_s_proto.as_ref().unwrap().challenge_contribution(
                &leg_enc.eph_pk_r.1,
                leg_enc.eph_pk_r.0.as_ref().unwrap(),
                &mut transcript,
            )?;
        }

        for i in 0..l.len() {
            pk_en_proto[i].0.challenge_contribution(
                &re_randomized_points.re_randomized_points[i + 1],
                &blinding_base,
                &leg_enc.eph_pk_enc_keys[i].0,
                &mut transcript,
            )?;
            pk_en_proto[i].1.challenge_contribution(
                &b_base,
                &re_randomized_points.blindings_with_different_gen[&(i + 1)],
                &mut transcript,
            )?;
            pk_en_proto[i].2.challenge_contribution(
                &leg_enc.eph_pk_enc_keys[i].0,
                &leg_enc.eph_pk_enc_keys[i].1,
                &mut transcript,
            )?;
            pk_en_proto[i].3.challenge_contribution(
                &leg_enc.eph_pk_enc_keys[i].0,
                &leg_enc.eph_pk_enc_keys[i].2,
                &mut transcript,
            )?;
            pk_en_proto[i].4.challenge_contribution(
                &leg_enc.eph_pk_enc_keys[i].0,
                leg_enc.eph_pk_enc_keys[i].3.as_ref().unwrap(),
                &mut transcript,
            )?;
        }

        for i in 0..r_meds.len() {
            let y = leg_enc.ct_meds[i]
                + asset_comm_params.j_0
                + (asset_comm_params.j_1 * F0::from(leg_enc.eph_pk_med_keys[i].0))
                - re_randomized_points.re_randomized_points[l.len() + i + 1];
            pk_m_proto[i].0.challenge_contribution(
                &enc_key_gen,
                &blinding_base,
                &y.into_affine(),
                &mut transcript,
            )?;

            pk_m_proto[i].1.challenge_contribution(
                &b_base,
                &re_randomized_points.re_randomized_points[1 + l.len() + i],
                &mut transcript,
            )?;

            let base = &leg_enc.eph_pk_enc_keys[leg_enc.eph_pk_med_keys[i].0 as usize].0;
            pk_m_proto[i].2.challenge_contribution(
                &base,
                &leg_enc.eph_pk_med_keys[i].1,
                &mut transcript,
            )?;
        }

        for i in 0..leg.public_enc_keys.len() {
            eph_pk_public_enc_proto[i].0.challenge_contribution(
                &leg.public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].0,
                &mut transcript,
            )?;
            eph_pk_public_enc_proto[i].1.challenge_contribution(
                &leg.public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].1,
                &mut transcript,
            )?;
            eph_pk_public_enc_proto[i].2.challenge_contribution(
                &leg.public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].2,
                &mut transcript,
            )?;
        }

        t_asset_id.challenge_contribution(
            &asset_comm_params.j_0,
            &tree_parameters.odd_parameters.pc_gens().B_blinding,
            &re_randomized_points.re_randomized_points[0],
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<F0>(LEG_TXN_CHALLENGE_LABEL);

        // For this commitment, the witness will extra blinding from BP
        wits.insert(0, comm_r_i_blinding);
        let resp_comm_r_i_amount = t_comm_r_i_amount.response(&wits, &challenge)?;

        // Responses for various r_i and its variations and amount are present in response for t_comm_r_i_amount
        let resp_ct_s = ct_s_proto.gen_partial_proof();
        let resp_ct_r = ct_r_proto.gen_partial_proof();
        let resp_amount_enc = ct_amount_proto.gen_partial_proof();
        let resp_asset_id_enc = ct_asset_id_proto.gen_partial_proof();
        let resp_eph_pk_s_v = eph_pk_s_v_proto.gen_partial_proof();
        let resp_eph_pk_s_at = eph_pk_s_at_proto.gen_partial_proof();
        let resp_eph_pk_r_v = eph_pk_r_v_proto.gen_partial_proof();
        let resp_eph_pk_r_at = eph_pk_r_at_proto.gen_partial_proof();

        let resp_eph_pk_s_r = eph_pk_s_r_proto.map(|p| p.gen_partial_proof());
        let resp_eph_pk_r_s = eph_pk_r_s_proto.map(|p| p.gen_partial_proof());

        let resp_eph_pk_enc = pk_en_proto
            .into_iter()
            .map(|(p_0, p_1, p_2, p_3, p_4)| {
                (
                    p_0.gen_partial_proof(),
                    p_1.gen_partial_proof(),
                    p_2.gen_partial_proof(),
                    p_3.gen_partial_proof(),
                    p_4.gen_partial_proof(),
                )
            })
            .collect();

        let resp_eph_pk_meds = pk_m_proto
            .into_iter()
            .map(|(p_0, p_1, p_2)| {
                (
                    p_0.gen_partial2_proof(&challenge),
                    p_1.gen_partial_proof(),
                    p_2.gen_partial_proof(),
                )
            })
            .collect();

        // Generate responses for public encryption key proofs
        let resp_eph_pk_public_enc = eph_pk_public_enc_proto
            .into_iter()
            .map(|(p_0, p_1, p_2)| {
                (
                    p_0.gen_partial_proof(),
                    p_1.gen_partial_proof(),
                    p_2.gen_partial_proof(),
                )
            })
            .collect();

        Zeroize::zeroize(&mut wits);
        Zeroize::zeroize(&mut comm_r_i_blinding);
        Zeroize::zeroize(&mut r_1);
        Zeroize::zeroize(&mut r_2);
        Zeroize::zeroize(&mut r_3);
        Zeroize::zeroize(&mut r_4);
        Zeroize::zeroize(&mut r_1_inv);
        Zeroize::zeroize(&mut r_2_inv);
        Zeroize::zeroize(&mut r_2_r_1_inv);
        Zeroize::zeroize(&mut r_3_r_1_inv);
        Zeroize::zeroize(&mut r_3_r_2_inv);
        Zeroize::zeroize(&mut r_4_r_1_inv);
        Zeroize::zeroize(&mut r_4_r_2_inv);
        Zeroize::zeroize(&mut r_1_r_2_inv);
        Zeroize::zeroize(&mut amount);

        let resp_asset_id = t_asset_id.gen_proof(&challenge);

        Ok(Self {
            r1cs_proof: None,
            re_randomized_path,
            resp_amount_enc,
            resp_asset_id_enc,
            resp_asset_id,
            re_randomized_points,
            ped_comms,
            comm_r_i_amount,
            t_comm_r_i_amount: t_comm_r_i_amount.t,
            resp_comm_r_i_amount,
            resp_ct_s,
            resp_ct_r,
            resp_eph_pk_s_v,
            resp_eph_pk_s_at,
            resp_eph_pk_r_v,
            resp_eph_pk_r_at,
            resp_eph_pk_enc,
            resp_eph_pk_meds,
            resp_eph_pk_s_r,
            resp_eph_pk_r_s,
            resp_eph_pk_public_enc,
        })
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_tree_root: &Root<L, 1, G1, G0>,
        public_enc_keys: Vec<Affine<G0>>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
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

        let (even_tuple, odd_tuple) = self
            .verify_and_return_tuples::<R, Parameters0, Parameters1>(
                leg_enc,
                asset_tree_root,
                public_enc_keys,
                nonce,
                tree_parameters,
                asset_comm_params,
                enc_key_gen,
                enc_gen,
                rng,
                rmc_0,
            )?;

        handle_verification_tuples(even_tuple, odd_tuple, tree_parameters, rmc)
    }

    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_tree_root: &Root<L, 1, G1, G0>,
        public_enc_keys: Vec<Affine<G0>>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G1>>, VerificationTuple<Affine<G0>>)> {
        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        self.verify_sigma_protocols_and_enforce_constraints::<Parameters0, Parameters1>(
            leg_enc,
            asset_tree_root,
            public_enc_keys,
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

    pub fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_tree_root: &Root<L, 1, G1, G0>,
        public_enc_keys: Vec<Affine<G0>>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let re_randomized_path = self.re_randomized_path.as_ref().ok_or_else(|| {
            Error::ProofVerificationError(
                "re_randomized_path must be present when not using batched verification"
                    .to_string(),
            )
        })?;

        re_randomized_path.select_and_rerandomize_verifier_gadget::<Parameters1, Parameters0>(
            asset_tree_root,
            even_verifier,
            odd_verifier,
            tree_parameters,
        )?;

        add_to_transcript!(
            odd_verifier.transcript(),
            ROOT_LABEL,
            asset_tree_root,
            NONCE_LABEL,
            nonce,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path
        );

        let rerandomized_leaf = re_randomized_path.path.get_rerandomized_leaf();

        add_to_transcript!(odd_verifier.transcript(), LEG_ENC_LABEL, leg_enc,);

        self.verify_sigma_protocols_and_enforce_constraints_with_rerandomized_leaf::<Parameters0, Parameters1>(
            leg_enc, rerandomized_leaf,
            public_enc_keys,
            tree_parameters, asset_comm_params,
            enc_key_gen, enc_gen, even_verifier, odd_verifier, rmc,
        )
    }

    pub fn verify_sigma_protocols_and_enforce_constraints_with_rerandomized_leaf<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        rerandomized_leaf: Affine<G1>,
        public_enc_keys: Vec<Affine<G0>>,
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let asset_id_ciphertext = leg_enc.asset_id_ciphertext().ok_or_else(|| {
            Error::ProofVerificationError(
                "leg_enc.ct_asset_id must be ciphertext for LegCreationProof".to_string(),
            )
        })?;

        if asset_comm_params.comm_key.len() < self.re_randomized_points.len() {
            return Err(Error::InsufficientCommitmentKeyLength(
                asset_comm_params.comm_key.len(),
                self.re_randomized_points.len(),
            ));
        }
        let num_enc_keys = self.resp_eph_pk_enc.len();
        let num_med_keys = self.resp_eph_pk_meds.len();

        if leg_enc.eph_pk_enc_keys.len() != num_enc_keys {
            return Err(Error::ProofVerificationError(format!(
                "leg_enc.eph_pk_enc_keys.len() != resp_eph_pk_enc.len() ({} != {})",
                leg_enc.eph_pk_enc_keys.len(),
                num_enc_keys
            )));
        }
        if leg_enc.ct_meds.len() != num_med_keys {
            return Err(Error::ProofVerificationError(format!(
                "leg_enc.ct_meds.len() != resp_eph_pk_meds.len() ({} != {})",
                leg_enc.ct_meds.len(),
                num_med_keys
            )));
        }
        if leg_enc.eph_pk_med_keys.len() != num_med_keys {
            return Err(Error::ProofVerificationError(format!(
                "leg_enc.eph_pk_med_keys.len() != resp_eph_pk_meds.len() ({} != {})",
                leg_enc.eph_pk_med_keys.len(),
                num_med_keys
            )));
        }

        if self.resp_eph_pk_public_enc.len() != leg_enc.eph_pk_public_enc_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_eph_pk_public_enc.len() != leg_enc.eph_pk_public_enc_keys.len() ({} != {})",
                self.resp_eph_pk_public_enc.len(),
                leg_enc.eph_pk_public_enc_keys.len()
            )));
        }
        if self.resp_eph_pk_public_enc.len() != public_enc_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "resp_eph_pk_public_enc.len() != public_enc_keys.len() ({} != {})",
                self.resp_eph_pk_public_enc.len(),
                public_enc_keys.len()
            )));
        }

        if self.re_randomized_points.len() != num_enc_keys + num_med_keys + 1 {
            return Err(Error::DifferentNumberOfRandomizedPointsAndResponses(
                self.re_randomized_points.len(),
                num_enc_keys + num_med_keys + 1,
            ));
        }

        let parties_see_each_other = leg_enc.do_parties_see_each_other();
        if parties_see_each_other {
            if self.resp_eph_pk_s_r.is_none() || self.resp_eph_pk_r_s.is_none() {
                return Err(Error::ProofVerificationError(
                    "parties_see_each_other is true but resp_eph_pk_s_r/resp_eph_pk_r_s is missing"
                        .to_string(),
                ));
            }
            if leg_enc.eph_pk_s.1.is_none() || leg_enc.eph_pk_r.0.is_none() {
                return Err(Error::ProofVerificationError(
                    "parties_see_each_other is true but leg_enc.eph_pk_s.1/leg_enc.eph_pk_r.0 is missing"
                        .to_string(),
                ));
            }
        } else if self.resp_eph_pk_s_r.is_some() || self.resp_eph_pk_r_s.is_some() {
            return Err(Error::ProofVerificationError(
                "parties_see_each_other is false but resp_eph_pk_s_r/resp_eph_pk_r_s is present"
                    .to_string(),
            ));
        }

        let eph_pk_s_at = leg_enc.eph_pk_s.3.clone().ok_or_else(|| {
            Error::ProofVerificationError(
                "leg_enc.eph_pk_s.3 must be present when asset-id is encrypted".to_string(),
            )
        })?;
        let eph_pk_r_at = leg_enc.eph_pk_r.3.clone().ok_or_else(|| {
            Error::ProofVerificationError(
                "leg_enc.eph_pk_r.3 must be present when asset-id is encrypted".to_string(),
            )
        })?;

        for i in 0..num_enc_keys {
            if leg_enc.eph_pk_enc_keys[i].3.is_none() {
                return Err(Error::ProofVerificationError(format!(
                    "leg_enc.eph_pk_enc_keys[{i}].3 must be present when asset-id is encrypted"
                )));
            }
        }

        for i in 0..num_med_keys {
            let idx = leg_enc.eph_pk_med_keys[i].0 as usize;
            if idx >= num_enc_keys {
                return Err(Error::ProofVerificationError(format!(
                    "leg_enc.eph_pk_med_keys[{i}].0 is out of bounds for eph_pk_enc_keys ({} >= {})",
                    idx, num_enc_keys
                )));
            }
        }

        // If ct_s and ct_r need to be decrypted.
        let sender_receiver_decryption_needed = parties_see_each_other || num_enc_keys > 0;

        // +1 for blinding
        let num_resps = 1
            + 11
            + 2 * (num_enc_keys + num_med_keys)
            + if sender_receiver_decryption_needed {
                2
            } else {
                0
            };
        if self.resp_comm_r_i_amount.len() != num_resps {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                num_resps,
                self.resp_comm_r_i_amount.len(),
            ));
        }

        let mut key_indices = BTreeSet::new();
        for i in 0..(num_enc_keys + num_med_keys) {
            key_indices.insert(i + 1);
        }
        verify_ped_com::<_, _, _, _, Parameters1>(
            even_verifier,
            rerandomized_leaf,
            self.re_randomized_points.clone(),
            self.ped_comms.clone(),
            &tree_parameters.odd_parameters,
            key_indices,
        )?;

        let mut vars_count = 11 + (self.resp_eph_pk_enc.len() + self.resp_eph_pk_meds.len()) * 2;
        if sender_receiver_decryption_needed {
            vars_count += 2;
        }
        let vars = odd_verifier.commit_vec(vars_count, self.comm_r_i_amount);
        LegCreationProof::<L, F0, F1, G0, G1>::enforce_constraints(
            odd_verifier,
            None,
            sender_receiver_decryption_needed,
            num_enc_keys,
            num_med_keys,
            vars,
        )?;

        let mut transcript = odd_verifier.transcript();

        let blinding_base = -tree_parameters
            .odd_parameters
            .pc_gens()
            .B_blinding
            .into_group()
            .into_affine();

        let b_base = tree_parameters.odd_parameters.pc_gens().B;

        self.t_comm_r_i_amount
            .serialize_compressed(&mut transcript)?;

        self.resp_ct_s.challenge_contribution(
            &enc_key_gen,
            &leg_enc.eph_pk_s.0,
            &leg_enc.ct_s,
            &mut transcript,
        )?;

        self.resp_ct_r.challenge_contribution(
            &enc_key_gen,
            &leg_enc.eph_pk_r.1,
            &leg_enc.ct_r,
            &mut transcript,
        )?;

        self.resp_amount_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_amount,
            &mut transcript,
        )?;

        self.resp_asset_id_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &asset_id_ciphertext,
            &mut transcript,
        )?;

        self.resp_eph_pk_s_v.challenge_contribution(
            &leg_enc.eph_pk_s.0,
            &leg_enc.eph_pk_s.2,
            &mut transcript,
        )?;

        self.resp_eph_pk_s_at.challenge_contribution(
            &leg_enc.eph_pk_s.0,
            &eph_pk_s_at,
            &mut transcript,
        )?;

        self.resp_eph_pk_r_v.challenge_contribution(
            &leg_enc.eph_pk_r.1,
            &leg_enc.eph_pk_r.2,
            &mut transcript,
        )?;

        self.resp_eph_pk_r_at.challenge_contribution(
            &leg_enc.eph_pk_r.1,
            &eph_pk_r_at,
            &mut transcript,
        )?;

        if parties_see_each_other {
            let resp_eph_pk_s_r = self.resp_eph_pk_s_r.as_ref().ok_or_else(|| {
                Error::ProofVerificationError(
                    "resp_eph_pk_s_r must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;
            let resp_eph_pk_r_s = self.resp_eph_pk_r_s.as_ref().ok_or_else(|| {
                Error::ProofVerificationError(
                    "resp_eph_pk_r_s must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;
            let eph_pk_s_r = leg_enc.eph_pk_s.1.clone().ok_or_else(|| {
                Error::ProofVerificationError(
                    "leg_enc.eph_pk_s.1 must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;
            let eph_pk_r_s = leg_enc.eph_pk_r.0.clone().ok_or_else(|| {
                Error::ProofVerificationError(
                    "leg_enc.eph_pk_r.0 must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;

            resp_eph_pk_s_r.challenge_contribution(
                &leg_enc.eph_pk_s.0,
                &eph_pk_s_r,
                &mut transcript,
            )?;
            resp_eph_pk_r_s.challenge_contribution(
                &leg_enc.eph_pk_r.1,
                &eph_pk_r_s,
                &mut transcript,
            )?;
        }

        for i in 0..num_enc_keys {
            let (p_0, p_1, p_2, p_3, p_4) = &self.resp_eph_pk_enc[i];
            p_0.challenge_contribution(
                &self.re_randomized_points.re_randomized_points[i + 1],
                &blinding_base,
                &leg_enc.eph_pk_enc_keys[i].0,
                &mut transcript,
            )?;
            p_1.challenge_contribution(
                &b_base,
                &self.re_randomized_points.blindings_with_different_gen[&(i + 1)],
                &mut transcript,
            )?;
            p_2.challenge_contribution(
                &leg_enc.eph_pk_enc_keys[i].0,
                &leg_enc.eph_pk_enc_keys[i].1,
                &mut transcript,
            )?;
            p_3.challenge_contribution(
                &leg_enc.eph_pk_enc_keys[i].0,
                &leg_enc.eph_pk_enc_keys[i].2,
                &mut transcript,
            )?;
            p_4.challenge_contribution(
                &leg_enc.eph_pk_enc_keys[i].0,
                leg_enc.eph_pk_enc_keys[i].3.as_ref().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "leg_enc.eph_pk_enc_keys[{i}].3 must be present when asset-id is encrypted"
                    ))
                })?,
                &mut transcript,
            )?;
        }

        for i in 0..num_med_keys {
            let (p_0, p_1, p_2) = &self.resp_eph_pk_meds[i];
            let y = leg_enc.ct_meds[i]
                + asset_comm_params.j_0
                + (asset_comm_params.j_1 * F0::from(leg_enc.eph_pk_med_keys[i].0))
                - self.re_randomized_points.re_randomized_points[num_enc_keys + i + 1];
            p_0.challenge_contribution(
                &enc_key_gen,
                &blinding_base,
                &y.into_affine(),
                &mut transcript,
            )?;

            p_1.challenge_contribution(
                &b_base,
                &self.re_randomized_points.re_randomized_points[num_enc_keys + i + 1],
                &mut transcript,
            )?;

            let base = &leg_enc.eph_pk_enc_keys[leg_enc.eph_pk_med_keys[i].0 as usize].0;
            p_2.challenge_contribution(&base, &leg_enc.eph_pk_med_keys[i].1, &mut transcript)?;
        }

        for i in 0..self.resp_eph_pk_public_enc.len() {
            let (p_0, p_1, p_2) = &self.resp_eph_pk_public_enc[i];
            p_0.challenge_contribution(
                &public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].0,
                &mut transcript,
            )?;
            p_1.challenge_contribution(
                &public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].1,
                &mut transcript,
            )?;
            p_2.challenge_contribution(
                &public_enc_keys[i],
                &leg_enc.eph_pk_public_enc_keys[i].2,
                &mut transcript,
            )?;
        }

        self.resp_asset_id.challenge_contribution(
            &asset_comm_params.j_0,
            &tree_parameters.odd_parameters.pc_gens().B_blinding,
            &self.re_randomized_points.re_randomized_points[0],
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<F0>(LEG_TXN_CHALLENGE_LABEL);

        verify_or_rmc_3!(
            rmc,
            self.resp_ct_s,
            "resp_ct_s verification failed",
            leg_enc.ct_s,
            enc_key_gen,
            leg_enc.eph_pk_s.0,
            &challenge,
            &self.resp_comm_r_i_amount.0[2],
            &self.resp_comm_r_i_amount.0[6],
        );

        verify_or_rmc_3!(
            rmc,
            self.resp_ct_r,
            "resp_ct_r verification failed",
            leg_enc.ct_r,
            enc_key_gen,
            leg_enc.eph_pk_r.1,
            &challenge,
            &self.resp_comm_r_i_amount.0[3],
            &self.resp_comm_r_i_amount.0[7],
        );

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

        verify_or_rmc_3!(
            rmc,
            self.resp_asset_id,
            "resp_asset_id verification failed",
            self.re_randomized_points.re_randomized_points[0],
            asset_comm_params.j_0,
            tree_parameters.odd_parameters.pc_gens().B_blinding,
            &challenge,
        );

        verify_or_rmc_3!(
            rmc,
            self.resp_asset_id_enc,
            "resp_asset_id_enc verification failed",
            asset_id_ciphertext,
            enc_key_gen,
            enc_gen,
            &challenge,
            &self.resp_comm_r_i_amount.0[5],
            &self.resp_asset_id.response1,
        );

        verify_or_rmc_2!(
            rmc,
            self.resp_eph_pk_s_v,
            "resp_eph_pk_s_v verification failed",
            leg_enc.eph_pk_s.2,
            leg_enc.eph_pk_s.0,
            &challenge,
            &self.resp_comm_r_i_amount.0[8],
        );

        verify_or_rmc_2!(
            rmc,
            self.resp_eph_pk_r_v,
            "resp_eph_pk_r_v verification failed",
            leg_enc.eph_pk_r.2,
            leg_enc.eph_pk_r.1,
            &challenge,
            &self.resp_comm_r_i_amount.0[9],
        );

        verify_or_rmc_2!(
            rmc,
            self.resp_eph_pk_s_at,
            "resp_eph_pk_s_at verification failed",
            eph_pk_s_at,
            leg_enc.eph_pk_s.0,
            &challenge,
            &self.resp_comm_r_i_amount.0[10],
        );

        verify_or_rmc_2!(
            rmc,
            self.resp_eph_pk_r_at,
            "resp_eph_pk_r_at verification failed",
            eph_pk_r_at,
            leg_enc.eph_pk_r.1,
            &challenge,
            &self.resp_comm_r_i_amount.0[11],
        );

        if parties_see_each_other {
            let resp_eph_pk_s_r = self.resp_eph_pk_s_r.as_ref().ok_or_else(|| {
                Error::ProofVerificationError(
                    "resp_eph_pk_s_r must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;
            let resp_eph_pk_r_s = self.resp_eph_pk_r_s.as_ref().ok_or_else(|| {
                Error::ProofVerificationError(
                    "resp_eph_pk_r_s must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;
            let eph_pk_s_r = leg_enc.eph_pk_s.1.clone().ok_or_else(|| {
                Error::ProofVerificationError(
                    "leg_enc.eph_pk_s.1 must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;
            let eph_pk_r_s = leg_enc.eph_pk_r.0.clone().ok_or_else(|| {
                Error::ProofVerificationError(
                    "leg_enc.eph_pk_r.0 must be present when parties_see_each_other is true"
                        .to_string(),
                )
            })?;

            verify_or_rmc_2!(
                rmc,
                resp_eph_pk_s_r,
                "resp_eph_pk_s_r verification failed",
                eph_pk_s_r,
                leg_enc.eph_pk_s.0,
                &challenge,
                &self.resp_comm_r_i_amount.0[12],
            );
            verify_or_rmc_2!(
                rmc,
                resp_eph_pk_r_s,
                "resp_eph_pk_r_s verification failed",
                eph_pk_r_s,
                leg_enc.eph_pk_r.1,
                &challenge,
                &self.resp_comm_r_i_amount.0[13],
            );
        }

        // Dont need to offset any responses as following will only execute if sender_receiver_decryption_needed = true

        for i in 0..num_enc_keys {
            let (p_0, p_1, p_2, p_3, p_4) = &self.resp_eph_pk_enc[i];
            verify_or_rmc_3!(
                rmc,
                p_0,
                format!("resp_eph_pk_enc[{}].0 verification failed", i),
                leg_enc.eph_pk_enc_keys[i].0,
                self.re_randomized_points.re_randomized_points[i + 1],
                blinding_base,
                &challenge,
                &self.resp_comm_r_i_amount.0[2],
                &self.resp_comm_r_i_amount.0[14 + (2 * i) + 1],
            );
            verify_or_rmc_2!(
                rmc,
                p_1,
                format!("resp_eph_pk_enc[{}].1 verification failed", i),
                self.re_randomized_points.blindings_with_different_gen[&(i + 1)],
                b_base,
                &challenge,
                &self.resp_comm_r_i_amount.0[14 + (2 * i)],
            );
            verify_or_rmc_2!(
                rmc,
                p_2,
                format!("resp_eph_pk_enc[{}].2 verification failed", i),
                leg_enc.eph_pk_enc_keys[i].1,
                leg_enc.eph_pk_enc_keys[i].0,
                &challenge,
                &self.resp_comm_r_i_amount.0[12],
            );
            verify_or_rmc_2!(
                rmc,
                p_3,
                format!("resp_eph_pk_enc[{}].3 verification failed", i),
                leg_enc.eph_pk_enc_keys[i].2,
                leg_enc.eph_pk_enc_keys[i].0,
                &challenge,
                &self.resp_comm_r_i_amount.0[8],
            );
            verify_or_rmc_2!(
                rmc,
                p_4,
                format!("resp_eph_pk_enc[{}].4 verification failed", i),
                leg_enc.eph_pk_enc_keys[i].3.clone().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "leg_enc.eph_pk_enc_keys[{i}].3 must be present when asset-id is encrypted"
                    ))
                })?,
                leg_enc.eph_pk_enc_keys[i].0,
                &challenge,
                &self.resp_comm_r_i_amount.0[10],
            );
        }

        for i in 0..num_med_keys {
            let (p_0, p_1, p_2) = &self.resp_eph_pk_meds[i];
            let y = leg_enc.ct_meds[i]
                + asset_comm_params.j_0
                + (asset_comm_params.j_1 * F0::from(leg_enc.eph_pk_med_keys[i].0))
                - self.re_randomized_points.re_randomized_points[num_enc_keys + i + 1];
            let med_key_idx = leg_enc.eph_pk_med_keys[i].0 as usize;
            if med_key_idx >= num_enc_keys {
                return Err(Error::ProofVerificationError(format!(
                    "leg_enc.eph_pk_med_keys[{i}].0 is out of bounds for eph_pk_enc_keys ({} >= {})",
                    med_key_idx, num_enc_keys
                )));
            }
            let base = leg_enc.eph_pk_enc_keys[med_key_idx].0;

            verify_or_rmc_3!(
                rmc,
                p_0,
                format!("resp_eph_pk_meds[{}].0 verification failed", i),
                y.into_affine(),
                enc_key_gen,
                blinding_base,
                &challenge,
                &self.resp_comm_r_i_amount.0[14 + 2 * num_enc_keys + (2 * i)],
            );

            verify_or_rmc_2!(
                rmc,
                p_1,
                format!("resp_eph_pk_meds[{}].1 verification failed", i),
                self.re_randomized_points.blindings_with_different_gen[&(num_enc_keys + i + 1)],
                b_base,
                &challenge,
                &p_0.response2,
            );

            verify_or_rmc_2!(
                rmc,
                p_2,
                format!("resp_eph_pk_meds[{}].2 verification failed", i),
                leg_enc.eph_pk_med_keys[i].1,
                base,
                &challenge,
                &self.resp_comm_r_i_amount.0[14 + 2 * num_enc_keys + (2 * i) + 1],
            );
        }

        // Verify public ephemeral keys for encryption keys: A[i][0] = pk_en[i] * r_1, A[i][1] = pk_en[i] * r_2, A[i][2] = pk_en[i] * r_3
        for i in 0..self.resp_eph_pk_public_enc.len() {
            let (p_0, p_1, p_2) = &self.resp_eph_pk_public_enc[i];
            verify_or_rmc_2!(
                rmc,
                p_0,
                format!("resp_eph_pk_public_enc[{}].0 verification failed", i),
                leg_enc.eph_pk_public_enc_keys[i].0,
                public_enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[2],
            );
            verify_or_rmc_2!(
                rmc,
                p_1,
                format!("resp_eph_pk_public_enc[{}].1 verification failed", i),
                leg_enc.eph_pk_public_enc_keys[i].1,
                public_enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[3],
            );
            verify_or_rmc_2!(
                rmc,
                p_2,
                format!("resp_eph_pk_public_enc[{}].2 verification failed", i),
                leg_enc.eph_pk_public_enc_keys[i].2,
                public_enc_keys[i],
                &challenge,
                &self.resp_comm_r_i_amount.0[4],
            );
        }

        verify_schnorr_resp_or_rmc!(
            rmc,
            self.resp_comm_r_i_amount,
            Self::bp_gens_vec(
                sender_receiver_decryption_needed,
                num_enc_keys,
                num_med_keys,
                tree_parameters,
            ),
            self.comm_r_i_amount,
            self.t_comm_r_i_amount,
            &challenge,
        );

        Ok(())
    }

    fn enforce_constraints<CS: ConstraintSystem<F0>>(
        cs: &mut CS,
        amount: Option<Balance>,
        sender_receiver_decryption_needed: bool,
        num_enc_keys: usize,
        num_med_keys: usize,
        mut committed_variables: Vec<Variable<F0>>,
    ) -> Result<()> {
        let mut vars_enc_keys = Vec::with_capacity(num_enc_keys);
        let mut vars_med_keys = Vec::with_capacity(num_med_keys);

        for _ in 0..num_med_keys {
            let m_i_r_1_inv = committed_variables.pop().unwrap();
            let m_i = committed_variables.pop().unwrap();
            vars_med_keys.push((m_i, m_i_r_1_inv));
        }
        for _ in 0..num_enc_keys {
            let l_i_r_1 = committed_variables.pop().unwrap();
            let l_i = committed_variables.pop().unwrap();
            vars_enc_keys.push((l_i, l_i_r_1));
        }
        let (var_r1_r2_inv, var_r2_r1_inv) = if sender_receiver_decryption_needed {
            (
                Some(committed_variables.pop().unwrap()),
                Some(committed_variables.pop().unwrap()),
            )
        } else {
            (None, None)
        };

        let var_r4_r2_inv = committed_variables.pop().unwrap();
        let var_r4_r1_inv = committed_variables.pop().unwrap();
        let var_r3_r2_inv = committed_variables.pop().unwrap();
        let var_r3_r1_inv = committed_variables.pop().unwrap();
        let var_r2_inv = committed_variables.pop().unwrap();
        let var_r1_inv = committed_variables.pop().unwrap();
        let var_r4 = committed_variables.pop().unwrap();
        let var_r3 = committed_variables.pop().unwrap();
        let var_r2 = committed_variables.pop().unwrap();
        let var_r1 = committed_variables.pop().unwrap();
        let var_amount = committed_variables.pop().unwrap();

        let lc_one = LinearCombination::from(Variable::One(PhantomData::<F0>));

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

        let lc_r4 = LinearCombination::from(var_r4);

        // r_1 * r_4/r_1 = r_4
        let (_, _, r4) = cs.multiply(lc_r1.clone(), var_r4_r1_inv.into());
        cs.constrain(lc_r4.clone() - r4);

        // r_2 * r_4/r_2 = r_4
        let (_, _, r4) = cs.multiply(lc_r2.clone(), var_r4_r2_inv.into());
        cs.constrain(lc_r4.clone() - r4);

        if sender_receiver_decryption_needed {
            // r_1 * r_2/r_1 = r_2
            let (_, _, r2) = cs.multiply(lc_r1.clone(), var_r2_r1_inv.unwrap().into());
            cs.constrain(lc_r2.clone() - r2);

            // r_2 * r_1/r_2 = r_1
            let (_, _, r1) = cs.multiply(lc_r2.clone(), var_r1_r2_inv.unwrap().into());
            cs.constrain(lc_r1.clone() - r1);
        }

        for (l_i, l_i_r_1) in vars_enc_keys {
            // r_1 * l_i = l_i_r_1
            let (_, _, l_i_r_1_) = cs.multiply(lc_r1.clone(), l_i.into());
            cs.constrain(l_i_r_1 - l_i_r_1_);
        }

        for (m_i, m_i_r_1_inv) in vars_med_keys {
            // r_1 * m_i_r_1_inv = m_i
            let (_, _, m_i_) = cs.multiply(lc_r1.clone(), m_i_r_1_inv.into());
            cs.constrain(m_i - m_i_);
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

    fn bp_gens_vec<Parameters0: DiscreteLogParameters, Parameters1: DiscreteLogParameters>(
        sender_receiver_decryption_needed: bool,
        num_enc_keys: usize,
        num_med_keys: usize,
        tree_params: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
    ) -> Vec<Affine<G0>> {
        let count = 11
            + 2 * (num_enc_keys + num_med_keys)
            + if sender_receiver_decryption_needed {
                2
            } else {
                0
            };
        let mut gens = vec![tree_params.odd_parameters.pc_gens().B_blinding];
        for g in bp_gens_for_vec_commitment(count as u32, tree_params.odd_parameters.bp_gens()) {
            gens.push(g);
        }
        gens
    }
}

pub(crate) fn ensure_leg_encryption_consistent<G0: SWCurveConfig>(
    leg: &Leg<Affine<G0>>,
    leg_enc: &LegEncryption<Affine<G0>>,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        // Check consistency between leg and leg_enc fields
        if leg_enc.eph_pk_enc_keys.len() != leg.enc_keys.len() {
            return Err(Error::ProofGenerationError(format!(
                "Mismatch in eph_pk_enc_keys length: leg_enc has {} but leg has {} enc_keys",
                leg_enc.eph_pk_enc_keys.len(),
                leg.enc_keys.len()
            )));
        }

        if leg_enc.eph_pk_public_enc_keys.len() != leg.public_enc_keys.len() {
            return Err(Error::ProofGenerationError(format!(
                "Mismatch in eph_pk_public_enc_keys length: leg_enc has {} but leg has {} public_enc_keys",
                leg_enc.eph_pk_public_enc_keys.len(),
                leg.public_enc_keys.len()
            )));
        }

        if leg_enc.ct_meds.len() != leg.med_keys.len() {
            return Err(Error::ProofGenerationError(format!(
                "Mismatch in ct_meds length: leg_enc has {} but leg has {} med_keys",
                leg_enc.ct_meds.len(),
                leg.med_keys.len()
            )));
        }

        if leg_enc.eph_pk_med_keys.len() != leg.med_keys.len() {
            return Err(Error::ProofGenerationError(format!(
                "Mismatch in eph_pk_med_keys length: leg_enc has {} but leg has {} med_keys",
                leg_enc.eph_pk_med_keys.len(),
                leg.med_keys.len()
            )));
        }

        Ok(())
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
