use crate::util::{bp_gens_for_vec_commitment, BPProof, get_verification_tuples_with_rng, prove_with_rng, handle_verification_tuples};
use crate::{Error, ROOT_LABEL, add_to_transcript, error::Result};
use crate::{LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL};
use ark_dlog_gadget::dlog::{DiscreteLogParameters, DivisorComms};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{string::ToString, vec, vec::Vec};
use bulletproofs::r1cs::{
    ConstraintSystem, Prover, VerificationTuple, Verifier,
};
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::ped_comm_group_elems::{prove as prove_ped_com, verify as verify_ped_com};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, BALANCE_BITS, Balance, MAX_ASSET_ID, MAX_BALANCE};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{PartialPokPedersenCommitment};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;
use curve_tree_relations::parameters::{SelRerandProofParametersNew};
pub use crate::leg::{
    AssetCommitmentParams, AssetData, EphemeralPublicKey, Leg, LegEncryption,
    LegEncryptionRandomness, MediatorTxnProof, RespEphemeralPublicKey,
    LEG_TXN_CHALLENGE_LABEL, LEG_TXN_EVEN_LABEL, LEG_TXN_ODD_LABEL,
};

/// New proof structure that includes divisor commitments for the new curve tree protocol
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegCreationProofNew<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub r1cs_proof: Option<BPProof<G1, G0>>,
    pub re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G1, G0>>,
    pub resp_amount_enc: PartialPokPedersenCommitment<Affine<G0>>,
    pub resp_asset_id_enc: PartialPokPedersenCommitment<Affine<G0>>,
    pub resp_asset_id: PokPedersenCommitment<Affine<G0>>,
    pub ped_comms: Vec<DivisorComms<Affine<G1>>>,
    pub re_randomized_points: Vec<Affine<G0>>,
    pub comm_r_i_amount: Affine<G0>,
    pub t_comm_r_i_amount: Affine<G0>,
    pub resp_comm_r_i_amount: SchnorrResponse<Affine<G0>>,
    pub resp_eph_pk_auds_meds: Vec<RespEphemeralPublicKey<G0>>,
}

fn bp_gens_vec_new<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    Parameters0: DiscreteLogParameters,
    Parameters1: DiscreteLogParameters,
>(
    tree_parameters: &SelRerandProofParametersNew<G1, G0, Parameters1, Parameters0>,
) -> [Affine<G0>; 9] {
    let mut gens = bp_gens_for_vec_commitment(8, tree_parameters.odd_parameters.bp_gens());
    [
        tree_parameters.odd_parameters.pc_gens().B_blinding,
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

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> LegCreationProofNew<L, F0, F1, G0, G1>
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
    ) -> Result<Self> {
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
    ) -> Result<Self> {
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
    ) -> Result<Self> {

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
        crate::leg::LegCreationProof::<L, F0, F1, G0, G1>::enforce_constraints(odd_prover, Some(leg.amount), vars)?;

        Zeroize::zeroize(&mut wits);

        // Sigma protocol for proving knowledge of `comm_r_i_amount`
        let t_comm_r_i_amount = SchnorrCommitment::new(
            &LegCreationProofNew::<L, F0, F1, G0, G1>::bp_gens_vec::<Parameters0, Parameters1>(tree_parameters),
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
    ) -> Result<()> {
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
    ) -> Result<(VerificationTuple<Affine<G1>>, VerificationTuple<Affine<G0>>)> {
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
    ) -> Result<()> {
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

        verify_ped_com::<_, _, _, _, Parameters1>(
            even_verifier,
            rerandomized_leaf,
            self.re_randomized_points.clone(),
            self.ped_comms.clone(),
            &tree_parameters.odd_parameters,
        )?;

        let vars = odd_verifier.commit_vec(8, self.comm_r_i_amount);
        crate::leg::LegCreationProof::<L, F0, F1, G0, G1>::enforce_constraints(odd_verifier, None, vars)?;

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
                        bp_gens_vec_new(tree_parameters).to_vec(),
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
                    &bp_gens_vec_new(tree_parameters),
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

    pub(crate) fn bp_gens_vec<
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

/// New settlement proof structure using batched curve tree operations
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SettlementCreationProofNew<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub leg_proofs: Vec<LegCreationProofNew<L, F0, F1, G0, G1>>,
    pub re_randomized_paths: Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, G1, G0>>,
    pub r1cs_proof: Option<BPProof<G1, G0>>,
}

impl<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SettlementCreationProofNew<L, M, F0, F1, G0, G1>
{
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
    ) -> Result<Self> {
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
    ) -> Result<Self> {
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
            let leg_proof = LegCreationProofNew::new_with_given_prover_inner::<R, D0, Parameters0, Parameters1>(
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
    ) -> Result<()> {
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
    ) -> Result<(VerificationTuple<Affine<G1>>, VerificationTuple<Affine<G0>>)> {
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
    ) -> Result<()> {
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


#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::util::{add_verification_tuples_batches_to_rmc, batch_verify_bp, get_verification_tuples_with_rng, verify_rmc, verify_with_rng};
    use ark_pallas::{Fq as PallasBase, Fr as PallasScalar, PallasConfig};
    use ark_vesta::{Fr as VestaScalar, VestaConfig};
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use curve_tree_relations::curve_tree::CurveTree;
    use curve_tree_relations::parameters::SelRerandProofParametersNew;
    use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
    use ark_ec_divisors::{
        curves::{
            pallas::PallasParams, pallas::Point as PallasPoint, vesta::Point as VestaPoint,
            vesta::VestaParams,
        },
    };
    use std::time::Instant;

    type PallasParameters = PallasConfig;
    type VestaParameters = VestaConfig;
    type PallasF = PallasScalar;
    type VestaFr = PallasBase;
    type PallasFr = PallasScalar;


    #[test]
    fn leg_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        
        let label = b"asset-tree-params";
        let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 2;
        let num_mediators = 2;
        let asset_id = 1;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);

        let (sk_s_e, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
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
        
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.sl_params.delta,
        )
        .unwrap();

        let set = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set,
            &asset_tree_params,
            Some(4),
        );

        let amount = 100;
        let nonce = b"test-nonce";

        let clock = Instant::now();

        let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = asset_tree.root_node();

        let proof = LegCreationProofNew::<L, PallasF, VestaFr, PallasConfig, VestaParameters>::new::<
            _, PallasPoint, VestaPoint, PallasParams, VestaParams,
        >(
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
            .verify::<_, PallasParams, VestaParams>(
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
            .verify::<_, PallasParams, VestaParams>(
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

        println!("L={L}, height={}", asset_tree.height());
        println!(
            "total proof size = {}",
            proof.compressed_size() + leg_enc.compressed_size()
        );
        println!("total prover time = {:?}", prover_time);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular, verifier_time_rmc
        );
    }

    #[test]
    fn batch_leg_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;

        let label = b"asset-tree-params";
        let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 2;
        let num_mediators = 2;
        let batch_size = 5;

        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &asset_tree_params.even_parameters.bp_gens(),
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
                asset_tree_params.odd_parameters.sl_params.delta,
            )
            .unwrap();

            commitments.push(asset_data.commitment);
            asset_data_vec.push(asset_data);
        }

        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(4),
        );
        let root = asset_tree.root_node();

        let mut proofs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut nonces = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
             let nonce = format!("nonce_{}", i).into_bytes();
             let amount = (i + 100) as u64;
             let asset_id = (i + 1) as u32;

             let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
             let (leg_enc, leg_enc_rand) = leg.encrypt::<_, Blake2b512>(
                &mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen
             ).unwrap();

             let path = asset_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

            let proof = LegCreationProofNew::<L, PallasF, VestaFr, PallasConfig, VestaParameters>::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
                &mut rng,
                leg,
                leg_enc.clone(),
                leg_enc_rand,
                path,
                asset_data_vec[i].clone(),
                &root,
                &nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,

            ).unwrap();

            proofs.push(proof);
            leg_encs.push(leg_enc);
            nonces.push(nonce);
        }

        let clock = Instant::now();

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            proofs[i]
                .verify::<_, PallasParams, VestaParams>(
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
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
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

        batch_verify_bp(even_tuples, odd_tuples, asset_tree_params.even_parameters.pc_gens(), asset_tree_params.odd_parameters.pc_gens(), asset_tree_params.even_parameters.bp_gens(), asset_tree_params.odd_parameters.bp_gens()).unwrap();

        let batch_verifier_time = clock.elapsed();

        println!("L={L}, height={}", asset_tree.height());
        println!(
            "For {batch_size} leg verification proofs, verifier time = {:?}, batch verifier time {:?}",
            verifier_time, batch_verifier_time
        );

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples::<_, PallasParams, VestaParams>(
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
            asset_tree_params.even_parameters.pc_gens(),
            asset_tree_params.odd_parameters.pc_gens(),
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
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
    fn settlement_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 14;
        const L: usize = 64;
        const M: usize = 2;

        let height = 6;

        let label = b"test";
        let asset_tree_params =
            SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
                label,
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 1;
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let asset_id_1 = 1;
        let asset_id_2 = 2;
        let asset_id_3 = 3;
        let asset_id_4 = 4;
        let asset_id_5 = 5;

        // Setup keys for 2 pairs of sender/receiver
        let (_sk_s1, pk_s1) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_s_e1) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r1) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r_e1) = keygen_enc(&mut rng, enc_key_gen);

        let (_, pk_s2) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_s_e2) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r2) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r_e2) = keygen_enc(&mut rng, enc_key_gen);

        // Auditor key
        let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys = vec![(true, pk_a_e.0)];
        // Create 5 asset data entries with different asset IDs
        let mut asset_data = Vec::new();
        let mut commitments = Vec::new();
        for i in 0..5 {
            let asset_id = (i + 1) as u32;
            let ad = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.sl_params.delta,
            )
            .unwrap();
            commitments.push(ad.commitment);
            asset_data.push(ad);
        }

        // Create the asset tree with all asset data
        let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(height),
        );

        let root = asset_tree.root_node();
        let amount = 100;
        let nonce = b"test-nonce";

        // Create 2 legs
        let leg_1 = Leg::new(pk_s1.0, pk_r1.0, keys.clone(), amount, asset_id_1).unwrap();
        let leg_2 = Leg::new(pk_s2.0, pk_r2.0, keys.clone(), amount, asset_id_2).unwrap();

        let (leg_enc1, leg_enc_rand1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e1.0, pk_r_e1.0, enc_key_gen, enc_gen)
            .unwrap();
        let (leg_enc2, leg_enc_rand2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e2.0, pk_r_e2.0, enc_key_gen, enc_gen)
            .unwrap();

        let path_1 = asset_tree.get_paths_to_leaves(&[0, 1]).unwrap();

        println!("For tree with height {height}, L={L}, M={M}");

        println!("For 2 leg settlement");

        let clock = Instant::now();
        let proof = SettlementCreationProofNew::<L, M, _, _, _, _>::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
            &mut rng,
            vec![leg_1.clone(), leg_2.clone()],
            vec![leg_enc1.clone(), leg_enc2.clone()],
            vec![leg_enc_rand1.clone(), leg_enc_rand2.clone()],
            vec![path_1.clone()],
            vec![asset_data[0].clone(), asset_data[1].clone()],
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                vec![leg_enc1.clone(), leg_enc2.clone()],
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifying_time = clock.elapsed();

        println!(
            "Proving time: {:?}, verifying time: {:?}, proof size {}",
            proving_time,
            verifying_time,
            proof.compressed_size()
        );

        // Create 2 more legs
        let leg_3 = Leg::new(pk_s1.0, pk_r1.0, keys.clone(), amount, asset_id_3).unwrap();
        let leg_4 = Leg::new(pk_s2.0, pk_r2.0, keys.clone(), amount, asset_id_4).unwrap();

        let (leg_enc3, leg_enc_rand3) = leg_3
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e1.0, pk_r_e1.0, enc_key_gen, enc_gen)
            .unwrap();
        let (leg_enc4, leg_enc_rand4) = leg_4
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e2.0, pk_r_e2.0, enc_key_gen, enc_gen)
            .unwrap();

        let path_2 = asset_tree.get_paths_to_leaves(&[2, 3]).unwrap();

        println!("For 4 leg settlement");

        let clock = Instant::now();
        let proof = SettlementCreationProofNew::<L, M, _, _, _, _>::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
            &mut rng,
            vec![leg_1.clone(), leg_2.clone(), leg_3.clone(), leg_4.clone()],
            vec![
                leg_enc1.clone(),
                leg_enc2.clone(),
                leg_enc3.clone(),
                leg_enc4.clone(),
            ],
            vec![
                leg_enc_rand1.clone(),
                leg_enc_rand2.clone(),
                leg_enc_rand3.clone(),
                leg_enc_rand4.clone(),
            ],
            vec![path_1.clone(), path_2.clone()],
            vec![
                asset_data[0].clone(),
                asset_data[1].clone(),
                asset_data[2].clone(),
                asset_data[3].clone(),
            ],
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                ],
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifying_time = clock.elapsed();

        println!(
            "Proving time: {:?}, verifying time: {:?}, proof size {}",
            proving_time,
            verifying_time,
            proof.compressed_size()
        );

        // Create 1 more leg
        let leg_5 = Leg::new(pk_s1.0, pk_r1.0, keys.clone(), amount, asset_id_5).unwrap();
        let (leg_enc5, leg_enc_rand5) = leg_5
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e1.0, pk_r_e1.0, enc_key_gen, enc_gen)
            .unwrap();

        let path_3 = asset_tree.get_paths_to_leaves(&[4]).unwrap();

        println!("For 5 leg settlement");

        let clock = Instant::now();
        let proof = SettlementCreationProofNew::<L, M, _, _, _, _>::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
            &mut rng,
            vec![
                leg_1.clone(),
                leg_2.clone(),
                leg_3.clone(),
                leg_4.clone(),
                leg_5.clone(),
            ],
            vec![
                leg_enc1.clone(),
                leg_enc2.clone(),
                leg_enc3.clone(),
                leg_enc4.clone(),
                leg_enc5.clone(),
            ],
            vec![
                leg_enc_rand1.clone(),
                leg_enc_rand2.clone(),
                leg_enc_rand3.clone(),
                leg_enc_rand4.clone(),
                leg_enc_rand5.clone(),
            ],
            vec![path_1.clone(), path_2.clone(), path_3.clone()],
            vec![
                asset_data[0].clone(),
                asset_data[1].clone(),
                asset_data[2].clone(),
                asset_data[3].clone(),
                asset_data[4].clone(),
            ],
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                &mut rng,
                vec![
                    leg_enc1.clone(),
                    leg_enc2.clone(),
                    leg_enc3.clone(),
                    leg_enc4.clone(),
                    leg_enc5.clone(),
                ],
                &root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verifying_time = clock.elapsed();

        println!(
            "Proving time: {:?}, verifying time: {:?}, proof size {}",
            proving_time,
            verifying_time,
            proof.compressed_size()
        );
    }

    #[test]
    fn batch_settlement_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 15;
        const L: usize = 64;
        const M: usize = 2; // Settlement supports M > 1
        
        let height = 4;

        let label = b"test";
        let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 1;
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let mut all_asset_data = Vec::new();
        let mut commitments = Vec::new();
        let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
        let keys = vec![(true, pk_a_e.0)];

        for i in 0..(M + 1) {
            let asset_id = (i + 1) as u32;
            let ad = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.sl_params.delta,
            )
            .unwrap();
            commitments.push(ad.commitment);
            all_asset_data.push(ad);
        }

        let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(height),
        );
        let root = asset_tree.root_node();

        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
        let amount = 100;
        
        let batch_size = 5;
        let mut nonces = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
             nonces.push(format!("nonce_{}", i).into_bytes());
        }

        let mut proofs = Vec::with_capacity(batch_size);
        let mut all_leg_encs = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
             let num_legs = match i % 3 {
                0 => M - 1,
                1 => M,
                _ => M + 1,
            };

            let mut legs = Vec::new();
            let mut leg_encs = Vec::new();
            let mut leg_enc_rands = Vec::new();
            let mut leaf_paths = Vec::new();
            let mut asset_data = Vec::new();

            for j in 0..num_legs {
                 // Reuse all_asset_data in loop (wrap around logic if num_legs > all_asset_data.len(), but here num_legs <= M+1 so OK)
                 let ad_idx = j % all_asset_data.len();
                 let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, all_asset_data[ad_idx].id).unwrap();
                 let (leg_enc, leg_enc_rand) = leg.encrypt::<_, Blake2b512>(
                    &mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen
                 ).unwrap();
                 
                 legs.push(leg);
                 leg_encs.push(leg_enc);
                 leg_enc_rands.push(leg_enc_rand);
                 asset_data.push(all_asset_data[ad_idx].clone());
            }

             for chunk in (0..num_legs as u32).collect::<Vec<_>>().chunks(M) {
                let path = asset_tree.get_paths_to_leaves(chunk).unwrap();
                leaf_paths.push(path);
             }

            let proof = SettlementCreationProofNew::<L, M, _, _, _, _>::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
                &mut rng,
                legs,
                leg_encs.clone(),
                leg_enc_rands,
                leaf_paths,
                asset_data,
                &root,
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,

            ).unwrap();
            
            proofs.push(proof);
            all_leg_encs.push(leg_encs);
        }

        let clock = Instant::now();
        for i in 0..batch_size {
             proofs[i].verify(
                &mut rng,
                all_leg_encs[i].clone(),
                &root,
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                None
            ).unwrap();
        }
        let verifier_time = clock.elapsed();

        let clock = Instant::now();
        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    all_leg_encs[i].clone(),
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
        let batch_tuple_time = clock.elapsed();

        let clock = Instant::now();
        batch_verify_bp(even_tuples, odd_tuples, asset_tree_params.even_parameters.pc_gens(), asset_tree_params.odd_parameters.pc_gens(), asset_tree_params.even_parameters.bp_gens(), asset_tree_params.odd_parameters.bp_gens()).unwrap();
        let batch_bp_time = clock.elapsed();

        let clock = Instant::now();
        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);
        let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    all_leg_encs[i].clone(),
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

        let batch_tuple_rmc_time = clock.elapsed();

        let clock = Instant::now();
        add_verification_tuples_batches_to_rmc(
            even_tuples,
            odd_tuples,
            asset_tree_params.even_parameters.pc_gens(),
            asset_tree_params.odd_parameters.pc_gens(),
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let rmc_time = clock.elapsed();

        println!(
            "Verifier time = {:?}, batch tuple time {:?}, batch BP time {:?}, batch_tuple_rmc_time {:?}, batch_verifier_rmc_time {:?}",
            verifier_time, batch_tuple_time, batch_bp_time, batch_tuple_rmc_time, rmc_time
        );
    }

    #[test]
    fn large_settlement_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 17;
        const L: usize = 64;
        const M: usize = 8;
        
        let height = 4;

        let label = b"test";
        let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();



        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 1;
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
        let keys = vec![(true, pk_a_e.0)];

        // Create single asset data
        let asset_id = 1;
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.sl_params.delta,
        )
        .unwrap();

        let commitments = vec![asset_data.commitment];

        let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(height),
        );
        let root = asset_tree.root_node();

        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
        let amount = 100;
        let nonce = b"test-nonce";
        
        // Reduced num_legs as per user request to avoid "Not enough labels" error
        let num_legs = 30;
        let mut legs = Vec::with_capacity(num_legs);
        let mut leg_encs = Vec::with_capacity(num_legs);
        let mut leg_enc_rands = Vec::with_capacity(num_legs);
        let mut asset_data_vec = Vec::with_capacity(num_legs);

        for _ in 0..num_legs {
             let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
             let (leg_enc, leg_enc_rand) = leg.encrypt::<_, Blake2b512>(
                &mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen
             ).unwrap();
             
             legs.push(leg);
             leg_encs.push(leg_enc);
             leg_enc_rands.push(leg_enc_rand);
             asset_data_vec.push(asset_data.clone());
        }

        let mut paths = Vec::new();
        // All legs use the same asset (index 0)
        let indices = vec![0; num_legs];
        for chunk in indices.chunks(M) {
            let path = asset_tree.get_paths_to_leaves(chunk).unwrap();
            paths.push(path);
        }

        println!("For tree with height {height}, L={L}, M={M} and {num_legs} legs");

        let clock = Instant::now();
        let proof = SettlementCreationProofNew::<L, M, _, _, _, _>::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
            &mut rng,
            legs,
            leg_encs.clone(),
            leg_enc_rands,
            paths,
            asset_data_vec,
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,

        ).unwrap();
        let proving_time = clock.elapsed();
        
        let mut rmc_1 = RandomizedMultChecker::new(VestaScalar::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(PallasScalar::rand(&mut rng));

        let clock = Instant::now();
        proof.verify(
            &mut rng,
            leg_encs,
            &root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,

            Some((&mut rmc_1, &mut rmc_0))
        ).unwrap();
        
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let verifying_time = clock.elapsed();
        
        println!(
            "Proving time: {:?}, verifying time: {:?}, proof size: {} bytes",
            proving_time,
            verifying_time,
            proof.compressed_size()
        );
    }

    #[test]
    fn combined_leg_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 16;
        const L: usize = 64;

        let height = 4;

        let label = b"test";
        let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();



        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 2;
        let num_mediators = 3;
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);

        let keys_auditor = (0..num_auditors).map(|_| keygen_enc(&mut rng, enc_key_gen)).collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators).map(|_| keygen_enc(&mut rng, enc_key_gen)).collect::<Vec<_>>();
        let mut keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
        keys.extend(keys_auditor.iter().map(|(_, k)| (true, k.0)).into_iter());
        keys.extend(keys_mediator.iter().map(|(_, k)| (false, k.0)).into_iter());

        let batch_size = 5;
        let mut asset_data_vec = Vec::with_capacity(batch_size);
        let mut commitments = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let asset_data = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.sl_params.delta,
            )
            .unwrap();
            commitments.push(asset_data.commitment);
            asset_data_vec.push(asset_data);
        }

        let asset_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(height),
        );
        let root = asset_tree.root_node();
        let amount = 100;
        
        let mut legs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut leg_enc_rands = Vec::with_capacity(batch_size);
        let mut nonces = Vec::with_capacity(batch_size);
        
        for i in 0..batch_size {
            let asset_id = (i + 1) as u32;
            let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
            let (leg_enc, leg_enc_rand) = leg.encrypt::<_, Blake2b512>(
                &mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen
            ).unwrap();
            
            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);
            nonces.push(format!("nonce_{}", i).into_bytes());
        }

        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover = Prover::new(&asset_tree_params.even_parameters.pc_gens(), even_transcript);
        let mut odd_prover = Prover::new(&asset_tree_params.odd_parameters.pc_gens(), odd_transcript);

        let mut proofs = Vec::with_capacity(batch_size);
        let clock = Instant::now();

        for i in 0..batch_size {
            let path = asset_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
            
            let proof = LegCreationProofNew::<L, PallasF, VestaFr, PallasConfig, VestaParameters>::new_with_given_prover::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
                &mut rng,
                legs[i].clone(),
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                path,
                asset_data_vec[i].clone(),
                &root,
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,

            ).unwrap();
            proofs.push(proof);
        }

        let (even_bp, odd_bp) = prove_with_rng(even_prover, odd_prover, &asset_tree_params.even_parameters.bp_gens(), &asset_tree_params.odd_parameters.bp_gens(), &mut rng).unwrap();
        let prover_time = clock.elapsed();

        let clock = Instant::now();
        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(even_transcript);
        let mut odd_verifier = Verifier::new(odd_transcript);

        for i in 0..batch_size {
            proofs[i].verify_sigma_protocols_and_enforce_constraints(
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
            ).unwrap();
        }

        verify_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            asset_tree_params.even_parameters.pc_gens(),
            asset_tree_params.odd_parameters.pc_gens(),
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
            &mut rng
        ).unwrap();
        
        let verification_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        let root = asset_tree.root_node();
        for i in 0..batch_size {
            proofs[i]
                .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
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
            asset_tree_params.even_parameters.pc_gens(),
            asset_tree_params.odd_parameters.pc_gens(),
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let rmc_verification_time = clock.elapsed();
        
        println!("L={L}, height={}", asset_tree.height());
        println!("Combined leg proving time = {:?}", prover_time);
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

    #[test]
    fn combined_settlement_verification() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 17;
        const L: usize = 64;
        const M: usize = 8;
        
        let height = 4;

        let label = b"test";
        let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
            label,
            NUM_GENS as u32,
            NUM_GENS as u32,
        )
        .unwrap();

        let sig_key_gen = hash_to_pallas(label, b"sk-gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();

        let num_auditors = 1;
        let asset_comm_params = AssetCommitmentParams::<PallasParameters, VestaParameters>::new(
            b"asset-comm-params",
            num_auditors,
            &asset_tree_params.even_parameters.bp_gens(),
        );

        let mut all_asset_data = Vec::new();
        let mut commitments = Vec::new();
        let (_, pk_a_e) = keygen_enc(&mut rng, enc_key_gen);
        let keys = vec![(true, pk_a_e.0)];

        for i in 0..(M + 1) {
            let asset_id = (i + 1) as u32;
            let ad = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.sl_params.delta,
            )
            .unwrap();
            commitments.push(ad.commitment);
            all_asset_data.push(ad);
        }

        let asset_tree = CurveTree::<L, M, VestaParameters, PallasParameters>::from_leaves(
            &commitments,
            &asset_tree_params,
            Some(height),
        );
        let root = asset_tree.root_node();

        let (_, pk_s) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_r) = keygen_sig(&mut rng, sig_key_gen);
        let (_, pk_s_e) = keygen_enc(&mut rng, enc_key_gen);
        let (_, pk_r_e) = keygen_enc(&mut rng, enc_key_gen);
        let amount = 100;
        
        let batch_size = 3;
        let mut nonces = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
             nonces.push(format!("nonce_{}", i).into_bytes());
        }

        // Shared provers
        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover = Prover::new(&asset_tree_params.even_parameters.pc_gens(), even_transcript);
        let mut odd_prover = Prover::new(&asset_tree_params.odd_parameters.pc_gens(), odd_transcript);

        let mut proofs = Vec::with_capacity(batch_size);
        let mut all_leg_encs = Vec::with_capacity(batch_size);

        let clock = Instant::now();

        for i in 0..batch_size {
             let num_legs = match i % 3 {
                0 => M - 1,
                1 => M,
                _ => M + 1,
            };

            let mut legs = Vec::new();
            let mut leg_encs = Vec::new();
            let mut leg_enc_rands = Vec::new();
            let mut leaf_paths = Vec::new();
            let mut asset_data = Vec::new();

            for j in 0..num_legs {
                 // Reuse all_asset_data in loop
                 let ad_idx = j % all_asset_data.len();
                 let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, all_asset_data[ad_idx].id).unwrap();
                 let (leg_enc, leg_enc_rand) = leg.encrypt::<_, Blake2b512>(
                    &mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen
                 ).unwrap();
                 
                 legs.push(leg);
                 leg_encs.push(leg_enc);
                 leg_enc_rands.push(leg_enc_rand);
                 asset_data.push(all_asset_data[ad_idx].clone());
            }

             for chunk in (0..num_legs as u32).collect::<Vec<_>>().chunks(M) {
                let path = asset_tree.get_paths_to_leaves(chunk).unwrap();
                leaf_paths.push(path);
             }

            let proof = SettlementCreationProofNew::<L, M, _, _, _, _>::new_with_given_prover::<_, PallasPoint, VestaPoint, _, _>(
                &mut rng,
                legs,
                leg_encs.clone(),
                leg_enc_rands,
                leaf_paths,
                asset_data,
                &root,
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,

            ).unwrap();
            
            proofs.push(proof);
            all_leg_encs.push(leg_encs);
        }

        let (even_bp, odd_bp) = prove_with_rng(
            even_prover,
            odd_prover,
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
            &mut rng
        ).unwrap();
        let proving_time = clock.elapsed();
        
        // Shared verifiers
        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(even_transcript);
        let mut odd_verifier = Verifier::new(odd_transcript);

        let verify_sigma_clock = Instant::now();
        for i in 0..batch_size {
             proofs[i].verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                all_leg_encs[i].clone(),
                &root,
                &nonces[i],
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,

                None, 
            ).unwrap();
        }
        let sigma_constraints_time = verify_sigma_clock.elapsed();
        
        let bp_clock = Instant::now();
        // Verify R1CS proof
        verify_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            asset_tree_params.even_parameters.pc_gens(),
            asset_tree_params.odd_parameters.pc_gens(),
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
            &mut rng
        ).unwrap();
        let bp_verification_time = bp_clock.elapsed();

        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        let verify_sigma_rmc_clock = Instant::now();
        for i in 0..batch_size {
            proofs[i]
                .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                    all_leg_encs[i].clone(),
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
        let sigma_constraints_rmc_time = verify_sigma_rmc_clock.elapsed();

        let rmc_clock = Instant::now();
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
            asset_tree_params.even_parameters.pc_gens(),
            asset_tree_params.odd_parameters.pc_gens(),
            asset_tree_params.even_parameters.bp_gens(),
            asset_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let rmc_verification_time = rmc_clock.elapsed();

        println!(
            "Proving time = {:?}, sigma = {:?}, bp_only = {:?}, sigma_rmc = {:?}, rmc_only = {:?}, proof size = {} bytes",
            proving_time,
            sigma_constraints_time,
            bp_verification_time,
            sigma_constraints_rmc_time,
            rmc_verification_time,
            even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
        );
    }

    // Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

    #[cfg(feature = "ignore_prover_input_sanitation")]
    mod input_sanitation_disabled {
        use super::*;
        use crate::keys::{keygen_enc, keygen_sig};
        use ark_pallas::Affine as PallasA;
        use ark_std::UniformRand;
        use blake2::Blake2b512;

        #[test]
        fn settlement_proof_with_mismatched_asset_data() {
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 64;

            // Create public params (generators, etc)
            let asset_tree_params = SelRerandProofParametersNew::<VestaParameters, PallasParameters, _, _>::new_using_label(
                b"asset-tree-params",
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
                &asset_tree_params.even_parameters.bp_gens(),
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

            // Create asset_data with one asset_id
            let asset_data = AssetData::new(
                asset_id,
                keys.clone(),
                &asset_comm_params,
                asset_tree_params.odd_parameters.sl_params.delta,
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

            let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

            let root = asset_tree.root_node();

            let proof = LegCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
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

            let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

            let proof = LegCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
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

            let path = asset_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

            let proof = LegCreationProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
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
