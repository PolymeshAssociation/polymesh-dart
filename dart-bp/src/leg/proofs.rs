use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_ff::{PrimeField};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms, SelectAndRerandomizePathWithDivisorComms};
use schnorr_pok::partial::{Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment};
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use ark_dlog_gadget::dlog::{DiscreteLogParameters, DivisorComms};
use rand_core::CryptoRngCore;
use ark_ec_divisors::DivisorCurve;
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Prover, Variable, VerificationTuple, Verifier};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::ped_comm_group_elems::{prove as prove_ped_com, verify as verify_ped_com};
use zeroize::Zeroize;
use curve_tree_relations::range_proof::range_proof;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use polymesh_dart_common::{Balance, BALANCE_BITS};
use crate::{add_to_transcript, error, Error, LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL};
use crate::leg::{AssetCommitmentParams, AssetData, Leg, LegEncryption, LegEncryptionRandomness, LEG_TXN_CHALLENGE_LABEL, LEG_TXN_EVEN_LABEL, LEG_TXN_ODD_LABEL};
use crate::util::{bp_gens_for_vec_commitment, get_verification_tuples_with_rng, handle_verification_tuples, prove_with_rng, BPProof};

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
    pub re_randomized_points: Vec<Affine<G0>>,
    /// Bulletproof vector commitment to `[r_1, r_2, r_3, r_4, r_2/r_1, r_3/r_1, r_4/r_1, amount]`
    pub comm_r_i_amount: Affine<G0>,
    pub t_comm_r_i_amount: Affine<G0>,
    pub resp_comm_r_i_amount: SchnorrResponse<Affine<G0>>,
    /// Response for proving correctness of ephemeral public keys. Is in the same order as the keys in [`AssetData`]
    pub resp_eph_pk_auds_meds: Vec<RespEphemeralPublicKey<G0>>,
    pub ped_comms: Vec<DivisorComms<Affine<G1>>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> LegCreationProof<L, F0, F1, G0, G1>
{
    /// Creates a new proof using the new curve tree protocol with divisor commitments
    pub fn new<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
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
    ) -> error::Result<Self> {
        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover = Prover::new(&tree_parameters.even_parameters.sl_params.pc_gens(), even_transcript);
        let mut odd_prover = Prover::new(&tree_parameters.odd_parameters.sl_params.pc_gens(), odd_transcript);
        
        let mut proof = Self::new_with_given_prover::<R, D0, D1, Parameters0, Parameters1>(
            rng, leg, leg_enc, leg_enc_rand, leaf_path, asset_data, asset_tree_root,
            nonce, tree_parameters, asset_comm_params, enc_key_gen, enc_gen,
            &mut even_prover, &mut odd_prover,
        )?;

        let (even_proof, odd_proof) = prove_with_rng(even_prover, odd_prover, &tree_parameters.even_parameters.bp_gens(), &tree_parameters.odd_parameters.bp_gens(), rng)?;
        proof.r1cs_proof = Some(BPProof { even_proof, odd_proof });
        Ok(proof)
    }

    pub fn new_with_given_prover<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
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
    ) -> error::Result<Self> {
        let (re_randomized_path, re_randomization_of_leaf) =
            leaf_path.select_and_rerandomize_prover_gadget_new::<R, D1, D0, Parameters1, Parameters0>(
                even_prover, odd_prover, tree_parameters, rng
            )?;

        add_to_transcript!(
            odd_prover.transcript(),
            ROOT_LABEL, asset_tree_root,
            NONCE_LABEL, nonce,
            RE_RANDOMIZED_PATH_LABEL, re_randomized_path
        );

        add_to_transcript!(odd_prover.transcript(), LEG_ENC_LABEL, leg_enc,);

        let rerandomized_leaf = re_randomized_path.path.get_rerandomized_leaf();

        Self::new_with_given_prover_inner::<R, D0, Parameters0, Parameters1>(
            rng, leg, leg_enc, leg_enc_rand, rerandomized_leaf, re_randomization_of_leaf,
            asset_data, tree_parameters, asset_comm_params, enc_key_gen, enc_gen,
            even_prover, odd_prover, Some(re_randomized_path)
        )
    }

    fn new_with_given_prover_inner<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
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
    ) -> error::Result<Self> {

        let mut at = F0::from(leg.asset_id);
        let mut amount = F0::from(leg.amount);

        let num_asset_data_keys = asset_data.keys.len();

        let asset_data_points = AssetData::points(leg.asset_id, &asset_data.keys, &asset_comm_params);

        let num_asset_data_points = asset_data_points.len();

        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if cfg!(debug_assertions) {
            let x_coords = asset_data_points
                .clone()
                .into_iter()
                .map(|p| (tree_parameters.odd_parameters.sl_params.delta + p).into_affine().x)
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
        let (re_randomized_points, ped_comms) = prove_ped_com::<_, _, _, _, _, D0, Parameters1>(
            rng,
            even_prover,
            asset_data_points,
            &rerandomized_leaf,
            re_randomization_of_leaf,
            blindings_for_points.clone(),
            &tree_parameters.odd_parameters,
            &tree_parameters.even_parameters.bp_gens(),
        )?;

        Zeroize::zeroize(&mut re_randomization_of_leaf);

        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if cfg!(debug_assertions) {
            assert_eq!(
                re_randomized_points[0].into_group(),
                (asset_comm_params.j_0 * at)
                    + (tree_parameters.odd_parameters.pc_gens().B_blinding * blindings_for_points[0])
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
                    k + (tree_parameters.odd_parameters.pc_gens().B_blinding
                        * blindings_for_points[i + 1])
                )
            }
        }

        let LegEncryptionRandomness(mut r_1, mut r_2, mut r_3, mut r_4) = leg_enc_rand;

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
            &tree_parameters.odd_parameters.bp_gens(),
        );
        LegCreationProof::<L, F0, F1, G0, G1>::enforce_constraints(odd_prover, Some(leg.amount), vars)?;

        Zeroize::zeroize(&mut wits);

        // Sigma protocol for proving knowledge of `comm_r_i_amount`
        let t_comm_r_i_amount = SchnorrCommitment::new(
            &LegCreationProof::<L, F0, F1, G0, G1>::bp_gens_vec::<Parameters0, Parameters1>(tree_parameters),
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

        let mut r_1_protocol_base1 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r1 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r2 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r3 = Vec::with_capacity(num_asset_data_keys);
        let mut t_points_r4 = Vec::with_capacity(num_asset_data_keys);
        let aud_role_base = -asset_comm_params.j_0;
        let blinding_base = -(tree_parameters
            .odd_parameters
            .pc_gens()
            .B_blinding
            .into_group()
            .into_affine());
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
            &tree_parameters.odd_parameters.pc_gens().B_blinding,
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
            &tree_parameters.odd_parameters.pc_gens().B_blinding,
            &re_randomized_points[0],
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<F0>(LEG_TXN_CHALLENGE_LABEL);

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
            let resp_1 = t_points_r1.gen_partial2_proof(&challenge);
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

        let resp_amount_enc = t_amount_enc.gen_partial_proof();
        let resp_asset_id = t_asset_id.gen_proof(&challenge);
        let resp_asset_id_enc = t_asset_id_enc.gen_partial_proof();

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
            resp_eph_pk_auds_meds,
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
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        mut rmc: Option<(&mut RandomizedMultChecker<Affine<G1>>, &mut RandomizedMultChecker<Affine<G0>>)>,
    ) -> error::Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((_, rmc_0)) => Some(&mut **rmc_0),
            None => None,
        };
        
        let (even_tuple, odd_tuple) = self.verify_and_return_tuples::<R, Parameters0, Parameters1>(
            leg_enc, asset_tree_root, nonce, tree_parameters, asset_comm_params,
            enc_key_gen, enc_gen, rng, rmc_0,
        )?;

        handle_verification_tuples(
            even_tuple, odd_tuple, tree_parameters, rmc
        )
    }

    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> error::Result<(VerificationTuple<Affine<G1>>, VerificationTuple<Affine<G0>>)> {
        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        
        self.verify_sigma_protocols_and_enforce_constraints::<Parameters0, Parameters1>(
            leg_enc, asset_tree_root, nonce, tree_parameters, asset_comm_params,
            enc_key_gen, enc_gen, &mut even_verifier, &mut odd_verifier, rmc,
        )?;

        let r1cs_proof = self.r1cs_proof.as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof is missing".to_string()))?;
        get_verification_tuples_with_rng(
            even_verifier, odd_verifier,
            &r1cs_proof.even_proof, &r1cs_proof.odd_proof, rng,
        )
    }

    pub fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_tree_root: &Root<L, 1, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> error::Result<()> {
        let re_randomized_path = self.re_randomized_path.as_ref().ok_or_else(|| {
            Error::ProofVerificationError(
                "re_randomized_path must be present when not using batched verification".to_string()
            )
        })?;

        // Call new curve tree verifier function with divisor commitments
        re_randomized_path.select_and_rerandomize_verifier_gadget::<Parameters1, Parameters0>(
            asset_tree_root, even_verifier, odd_verifier, tree_parameters,
        )?;

        add_to_transcript!(
            odd_verifier.transcript(),
            ROOT_LABEL, asset_tree_root,
            NONCE_LABEL, nonce,
            RE_RANDOMIZED_PATH_LABEL, re_randomized_path
        );

        let rerandomized_leaf = re_randomized_path.path.get_rerandomized_leaf();

        add_to_transcript!(odd_verifier.transcript(), LEG_ENC_LABEL, leg_enc,);

        self.verify_sigma_protocols_and_enforce_constraints_with_rerandomized_leaf::<Parameters0, Parameters1>(
            leg_enc, rerandomized_leaf, tree_parameters, asset_comm_params,
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
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> error::Result<()> {
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

        verify_ped_com::<_, _, _, _, Parameters1>(
            even_verifier,
            rerandomized_leaf,
            self.re_randomized_points.clone(),
            self.ped_comms.clone(),
            &tree_parameters.odd_parameters,
        )?;

        let vars = odd_verifier.commit_vec(8, self.comm_r_i_amount);
        LegCreationProof::<L, F0, F1, G0, G1>::enforce_constraints(odd_verifier, None, vars)?;

        let mut transcript = odd_verifier.transcript();

        self.t_comm_r_i_amount
            .serialize_compressed(&mut transcript)?;

        let aud_role_base = -asset_comm_params.j_0;
        let blinding_base = -(tree_parameters
            .odd_parameters
            .pc_gens()
            .B_blinding
            .into_group()
            .into_affine());
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
            &tree_parameters.odd_parameters.pc_gens().B_blinding,
            &self.re_randomized_points[0],
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<F0>(LEG_TXN_CHALLENGE_LABEL);

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
                    tree_parameters.odd_parameters.pc_gens().B_blinding,
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
                    
                for i in 0..self.resp_eph_pk_auds_meds.len() {
                    let resp = &self.resp_eph_pk_auds_meds[i];
                    let D_r1 = &leg_enc.eph_pk_auds_meds[i].1.0;

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
                    &tree_parameters.odd_parameters.pc_gens().B_blinding,
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
                
                for i in 0..self.resp_eph_pk_auds_meds.len() {
                    let resp = &self.resp_eph_pk_auds_meds[i];
                    let D_r1 = &leg_enc.eph_pk_auds_meds[i].1.0;

                    if !resp.r_1.verify(
                        D_r1,
                        &r_1_protocol_base1[i],
                        &blinding_base,
                        &challenge,
                        &self.resp_comm_r_i_amount.0[1],
                    ) {
                        return Err(Error::ProofVerificationError(
                            ark_std::format!("resp r_1 verification failed for auditor/mediator {}", i),
                        ));
                    }
                    if !resp.r_2.verify(&leg_enc.eph_pk_auds_meds[i].1.1, D_r1, &challenge, &self.resp_comm_r_i_amount.0[5]) {
                        return Err(Error::ProofVerificationError(
                            ark_std::format!("resp r_2 verification failed for auditor/mediator {}", i),
                        ));
                    }
                    if !resp.r_3.verify(&leg_enc.eph_pk_auds_meds[i].1.2, D_r1, &challenge, &self.resp_comm_r_i_amount.0[6]) {
                        return Err(Error::ProofVerificationError(
                            ark_std::format!("resp r_3 verification failed for auditor/mediator {}", i),
                        ));
                    }
                    if !resp.r_4.verify(&leg_enc.eph_pk_auds_meds[i].1.3, D_r1, &challenge, &self.resp_comm_r_i_amount.0[7]) {
                        return Err(Error::ProofVerificationError(
                            ark_std::format!("resp r_4 verification failed for auditor/mediator {}", i),
                        ));
                    }
                }
            }
        }

        Ok(())
    }

    fn enforce_constraints<CS: ConstraintSystem<F0>>(
        cs: &mut CS,
        amount: Option<Balance>,
        mut committed_variables: Vec<Variable<F0>>,
    ) -> error::Result<()> {
        let var_amount = committed_variables.pop().unwrap();
        let var_r_4_r_1_inv = committed_variables.pop().unwrap();
        let var_r_3_r_1_inv = committed_variables.pop().unwrap();
        let var_r_2_r_1_inv = committed_variables.pop().unwrap();
        let var_r_4 = committed_variables.pop().unwrap();
        let var_r_3 = committed_variables.pop().unwrap();
        let var_r_2 = committed_variables.pop().unwrap();
        let var_r_1 = committed_variables.pop().unwrap();

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
            amount.map(|a| a as u128),
            BALANCE_BITS.into(),
        )?;
        Ok(())
    }

    fn bp_gens_vec<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        tree_params: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
    ) -> [Affine<G0>; 9] {
        let mut gens = bp_gens_for_vec_commitment(8, tree_params.odd_parameters.bp_gens());
        [
            tree_params.odd_parameters.pc_gens().B_blinding,
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

/// Proof for a settlement involving multiple legs.
/// This allows efficient batched curve tree operations across all legs.
///
/// # Type Parameters
/// * `L` - Tree height
/// * `M` - Maximum number of legs that can be batched together in a single curve tree proof
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SettlementCreationProof<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// Individual leg proofs
    pub leg_proofs: Vec<LegCreationProof<L, F0, F1, G0, G1>>,
    /// Collection of re-randomized paths for all legs in batches of size at most M
    pub re_randomized_paths: Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, G1, G0>>,
    /// When this is None, external [`R1CSProof`] will be used
    pub r1cs_proof: Option<BPProof<G1, G0>>,
}

impl<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SettlementCreationProof<L, M, F0, F1, G0, G1>
{
    /// Creates a settlement proof for multiple legs.
    /// This method creates new transcripts and provers internally, then generates the proof.
    pub fn new<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs: Vec<Leg<Affine<G0>>>,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        leg_enc_rands: Vec<LegEncryptionRandomness<G0::ScalarField>>,
        leaf_paths: Vec<CurveTreeWitnessMultiPath<L, M, G1, G0>>,
        asset_data: Vec<AssetData<F0, F1, G0, G1>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> error::Result<Self> {
        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover = Prover::new(&tree_parameters.even_parameters.pc_gens(), even_transcript);
        let mut odd_prover = Prover::new(&tree_parameters.odd_parameters.pc_gens(), odd_transcript);

        let mut proof = Self::new_with_given_prover::<R, D0, D1, Parameters0, Parameters1>(
            rng, legs, leg_encs, leg_enc_rands, leaf_paths, asset_data, asset_tree_root,
            nonce, tree_parameters, asset_comm_params, enc_key_gen, enc_gen,
            &mut even_prover, &mut odd_prover,
        )?;

        let (even_proof, odd_proof) = prove_with_rng(even_prover, odd_prover, &tree_parameters.even_parameters.bp_gens(), &tree_parameters.odd_parameters.bp_gens(), rng)?;
        proof.r1cs_proof = Some(BPProof { even_proof, odd_proof });
        Ok(proof)
    }

    /// Creates a settlement proof for multiple legs with given provers.
    /// This allows the caller to manage the provers and transcripts externally.
    ///
    /// The method uses batched curve tree operations for efficiency:
    /// - Calls `select_and_rerandomize_prover_gadget` once for all paths
    /// - Creates each leg proof with the pre-computed rerandomized leaves
    pub fn new_with_given_prover<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs: Vec<Leg<Affine<G0>>>,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        leg_enc_rands: Vec<LegEncryptionRandomness<G0::ScalarField>>,
        leaf_paths: Vec<CurveTreeWitnessMultiPath<L, M, G1, G0>>,
        asset_data: Vec<AssetData<F0, F1, G0, G1>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    ) -> error::Result<Self> {
        let num_legs = legs.len();
        if num_legs == 0 {
            return Err(Error::ProofGenerationError(
                "At least one leg is required to create a settlement proof".to_string(),
            ));
        }
        if num_legs != leg_encs.len()
            || num_legs != leg_enc_rands.len()
            || num_legs != asset_data.len()
        {
            return Err(Error::ProofGenerationError(
                "Mismatched number of legs, encryptions, randomness, and asset data".to_string(),
            ));
        }

        if leaf_paths
            .iter()
            .fold(0, |acc, path| acc + path.num_indices())
            != num_legs as u32
        {
            return Err(Error::ProofGenerationError(
                "Total number of paths in leaf_paths does not match number of legs".to_string(),
            ));
        }

        // Use batched_select_and_rerandomize_prover_gadget_new for efficiency
        add_to_transcript!(odd_prover.transcript(), ROOT_LABEL, asset_tree_root, NONCE_LABEL, nonce);

        for leg_enc in &leg_encs {
            add_to_transcript!(odd_prover.transcript(), LEG_ENC_LABEL, leg_enc,);
        }

        let mut re_randomized_paths = Vec::with_capacity(leaf_paths.len());
        let mut all_rerandomized_leaves = Vec::with_capacity(num_legs);

        for leaf_path in leaf_paths.iter() {
            let (re_randomized_path, randomizers) =
                leaf_path.batched_select_and_rerandomize_prover_gadget_new::<R, D1, D0, Parameters1, Parameters0>(
                    even_prover, odd_prover, tree_parameters, rng
                )?;

            add_to_transcript!(odd_prover.transcript(), RE_RANDOMIZED_PATH_LABEL, re_randomized_path);

            let rerandomized_leaves = re_randomized_path.path.get_rerandomized_leaves();
            all_rerandomized_leaves.extend(
                rerandomized_leaves.into_iter().zip(randomizers).map(|(l, r)| (l, r))
            );

            re_randomized_paths.push(re_randomized_path);
        }

        debug_assert!(all_rerandomized_leaves.len() == num_legs);

        // Create individual leg proofs using the pre-computed rerandomized leaves
        let mut leg_proofs = Vec::with_capacity(num_legs);
        for i in 0..num_legs {
            let leg_proof = LegCreationProof::new_with_given_prover_inner::<R, D0, Parameters0, Parameters1>(
                rng,
                legs[i].clone(),
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                all_rerandomized_leaves[i].0,
                all_rerandomized_leaves[i].1,
                asset_data[i].clone(),
                tree_parameters,
                asset_comm_params,
                enc_key_gen,
                enc_gen,
                even_prover,
                odd_prover,
                None, // re_randomized_path is stored separately in SettlementCreationProofNew
            )?;
            leg_proofs.push(leg_proof);
        }

        Ok(Self { leg_proofs, re_randomized_paths, r1cs_proof: None })
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        rng: &mut R,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        mut rmc: Option<(&mut RandomizedMultChecker<Affine<G1>>, &mut RandomizedMultChecker<Affine<G0>>)>,
    ) -> error::Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((_, rmc_0)) => Some(&mut **rmc_0),
            None => None,
        };
        
        let (even_tuple, odd_tuple) = self.verify_and_return_tuples::<R, Parameters0, Parameters1>(
            leg_encs, asset_tree_root, nonce, tree_parameters, asset_comm_params,
            enc_key_gen, enc_gen, rng, rmc_0,
        )?;

        handle_verification_tuples(
            even_tuple, odd_tuple, tree_parameters, rmc
        )
    }

    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> error::Result<(VerificationTuple<Affine<G1>>, VerificationTuple<Affine<G0>>)> {
        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        
        self.verify_sigma_protocols_and_enforce_constraints::<Parameters0, Parameters1>(
            leg_encs, asset_tree_root, nonce, tree_parameters, asset_comm_params,
            enc_key_gen, enc_gen, &mut even_verifier, &mut odd_verifier, rmc,
        )?;

        let r1cs_proof = self.r1cs_proof.as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof is missing".to_string()))?;
        get_verification_tuples_with_rng(
            even_verifier, odd_verifier,
            &r1cs_proof.even_proof, &r1cs_proof.odd_proof, rng,
        )
    }

    pub fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        nonce: &[u8],
        tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>, 
    ) -> error::Result<()> {
        let num_legs = self.leg_proofs.len();
        if num_legs != leg_encs.len() {
            return Err(Error::ProofVerificationError(
                "Mismatched number of leg proofs and encryptions".to_string(),
            ));
        }

        add_to_transcript!(
            odd_verifier.transcript(),
            ROOT_LABEL, asset_tree_root,
            NONCE_LABEL, nonce,
        );

        for leg_enc in &leg_encs {
            add_to_transcript!(odd_verifier.transcript(), LEG_ENC_LABEL, leg_enc,);
        }

        let mut all_rerandomized_leaves = Vec::with_capacity(num_legs);
        
        for re_randomized_path in self.re_randomized_paths.iter() {
            re_randomized_path.batched_select_and_rerandomize_verifier_gadget::<Parameters1, Parameters0>(
                asset_tree_root, even_verifier, odd_verifier, tree_parameters,
            )?;
            
            all_rerandomized_leaves.extend(re_randomized_path.path.get_rerandomized_leaves());

            add_to_transcript!(
                odd_verifier.transcript(),
                RE_RANDOMIZED_PATH_LABEL, re_randomized_path
            );
        }
        
        if all_rerandomized_leaves.len() != num_legs {
            return Err(Error::ProofVerificationError(
                "Total number of rerandomized leaves does not match number of legs".to_string(),
            ));
        }

        for i in 0..num_legs {
             self.leg_proofs[i].verify_sigma_protocols_and_enforce_constraints_with_rerandomized_leaf::<Parameters0, Parameters1>(
                leg_encs[i].clone(), all_rerandomized_leaves[i], tree_parameters, asset_comm_params,
                enc_key_gen, enc_gen, even_verifier, odd_verifier, rmc.as_deref_mut(),
            )?;
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