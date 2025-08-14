use ark_std::ops::Neg;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::ped_comm_group_elems::{prove_naive, verify_naive};
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::commitment::PedersenCommitmentKey;
use dock_crypto_utils::transcript::Transcript;
use rand_core::{CryptoRng, CryptoRngCore, RngCore};
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use polymesh_dart_common::{AssetId, AMOUNT_BITS, ASSET_ID_BITS};
use crate::eq_across_groups::Proof;
use crate::error::{Error, Result};
use crate::leg::{AssetCommitmentParams, AssetData, Leg, LegEncryption, LegEncryptionRandomness, RespLeafPoint, SETTLE_TXN_CHALLENGE_LABEL, SETTLE_TXN_EVEN_LABEL, SETTLE_TXN_INSTANCE_LABEL, SETTLE_TXN_ODD_LABEL};
use crate::util::{bp_gens_for_vec_commitment, initialize_curve_tree_prover, initialize_curve_tree_verifier, prove_with_rng, verify_with_rng};

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AssetData<F0, F1, G0, G1>
{
    pub fn new_alt(
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
        let points = Self::points_alt(&keys, params);
        let mut x_coords = points
            .into_iter()
            .map(|p| (delta + p).into_affine().x)
            .collect::<Vec<_>>();
        x_coords.push(F1::from(id));
        let commitment =
            G1::msm(&params.comm_key[..(keys.len() + 1)], x_coords.as_slice()).unwrap();
        Ok(Self {
            id,
            keys,
            commitment: commitment.into_affine(),
        })
    }

    fn points_alt(
        keys: &[(bool, Affine<G0>)],
        params: &AssetCommitmentParams<G0, G1>,
    ) -> Vec<Affine<G0>> {
        keys.iter().map(|(role, k)| {
            let role = if *role {
                params.j_0
            } else {
                Affine::<G0>::zero()
            };
            (role + *k).into_affine()
        }).collect()
    }

    // More efficient update methods can be added in future
}

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
    /// Commitment to randomness and response for proving knowledge of amount using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to amount is created for using with Bulletproofs
    pub t_amount_at: Affine<G0>,
    pub resp_amount_at: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in twisted Elgamal encryption of amount.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_amount_enc: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving asset-id in twisted Elgamal encryption of asset-id.
    /// Using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_asset_id_enc: PokPedersenCommitment<Affine<G0>>,
    // pub resp_asset_id: PokPedersenCommitment<Affine<G0>>,
    pub leaf_hat: Affine<G1>,
    pub split_at: Affine<G1>,
    pub eq_proof: Proof<Affine<G0>, Affine<G1>, 32, 192, 8, 29, 1>,
    pub re_randomized_points: Vec<Affine<G0>>,
    pub comm_amount_at: Affine<G0>,
    pub comm_r_i: Affine<G0>,
    pub t_comm_r_i: Affine<G0>,
    pub resp_comm_r_i: SchnorrResponse<Affine<G0>>,
    pub resp_leaf_points: Vec<RespLeafPoint<G0>>,
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

    pub fn new<R: RngCore + CryptoRng>(
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

        let r_amount_at = F0::rand(rng);
        let (comm_amount_at, mut vars) = odd_prover.commit_vec(&[amount, at], r_amount_at, &tree_parameters.odd_parameters.bp_gens);
        let var_amount = vars.remove(0);
        let var_at = vars.remove(0);

        // TODO: What if we do range proof outside circuit? Or using another protocol like Bulletproofs++?
        range_proof(
            &mut odd_prover,
            var_amount.into(),
            Some(leg.amount),
            AMOUNT_BITS.into(),
        )?;
        range_proof(
            &mut odd_prover,
            var_at.into(),
            Some(leg.asset_id as u64),
            ASSET_ID_BITS as usize,
        )?;

        let rerandomized_leaf = re_randomized_path.get_rerandomized_leaf();

        let asset_data_points =
            AssetData::points_alt(&asset_data.keys, &asset_comm_params);

        if cfg!(debug_assertions) {
            let mut x_coords = asset_data_points
                .clone()
                .into_iter()
                .map(|p| (tree_parameters.odd_parameters.delta + p).into_affine().x)
                .collect::<Vec<_>>();
            x_coords.push(F1::from(leg.asset_id));
            let commitment = G1::msm(
                &asset_comm_params.comm_key[..asset_data_points.len() + 1],
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

        let k1 = F1::rand(rng);
        let k2 = re_randomization_of_leaf - k1;
        let split_at = asset_comm_params.comm_key[asset_data_points.len()] * F1::from(leg.asset_id) + tree_parameters.even_parameters.pc_gens.B_blinding * k2;
        let leaf_hat = rerandomized_leaf.into_group() - split_at;
        let leaf_hat = leaf_hat.into_affine();
        let split_at = split_at.into_affine();
        let re_randomized_points = prove_naive(
            &mut even_prover,
            asset_data_points,
            &leaf_hat,
            k1,
            blindings_for_points.clone(),
            &tree_parameters.odd_parameters,
        )?;

        if cfg!(debug_assertions) {
            for i in 0..asset_data.keys.len() {
                let (r, k) = asset_data.keys[i];
                let k = if r {
                    asset_comm_params.j_0 + k
                } else {
                    k.into_group()
                };
                assert_eq!(
                    re_randomized_points[i].into_group(),
                    k + (tree_parameters.odd_parameters.pc_gens.B_blinding
                        * blindings_for_points[i])
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

        let comm_r_i_blinding = F0::rand(rng);
        let (comm_r_i, vars) = odd_prover.commit_vec(&[r_1, r_2, r_3, r_4, r_2_r_1_inv, r_3_r_1_inv, r_4_r_1_inv], comm_r_i_blinding, &tree_parameters.odd_parameters.bp_gens);
        crate::leg::SettlementTxnProof::<L, F0, F1, G0, G1>::enforce_constraints(&mut odd_prover, vars);

        let t_comm_r_i = SchnorrCommitment::new(&crate::leg::SettlementTxnProof::<L, F0, F1, G0, G1>::bp_gens_vec(tree_parameters), vec![
            F0::rand(rng),
            r_1_blinding,
            r_2_blinding,
            r_3_blinding,
            r_4_blinding,
            r_2_r_1_inv_blinding,
            r_3_r_1_inv_blinding,
            r_4_r_1_inv_blinding,
        ]);

        let mut transcript = odd_prover.transcript();

        let comm_key1 = PedersenCommitmentKey {g: enc_gen, h: enc_key_gen};
        let comm_key2 = PedersenCommitmentKey {g: asset_comm_params.comm_key[re_randomized_points.len()], h: tree_parameters.even_parameters.pc_gens.B_blinding};
        let eq_proof = Proof::<
            Affine<G0>,
            Affine<G1>,
            32,
            192,
            8,
            29,
            1,
        >::new(
            rng,
            &at,
            r_4,
            k2,
            &comm_key1,
            &comm_key2,
            transcript,
        )
            .unwrap();

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
            // let t_1 = SchnorrCommitment::new(&bases, blindings_r1);
            let t_1 = if *role {
                SchnorrCommitment::new(&[
                    re_randomized_points[i],
                    blinding_base,
                    aud_role_base,
                ], blindings_r1)
            } else {
                SchnorrCommitment::new(&[
                    re_randomized_points[i],
                    blinding_base,
                ], blindings_r1)
            };

            let t_2 = PokDiscreteLogProtocol::init(r_2_r_1_inv, r_2_r_1_inv_blinding, &leg_enc.eph_pk_auds_meds[i].0);
            let t_3 = PokDiscreteLogProtocol::init(r_3_r_1_inv, r_3_r_1_inv_blinding, &leg_enc.eph_pk_auds_meds[i].0);
            let t_4 = PokDiscreteLogProtocol::init(r_4_r_1_inv, r_4_r_1_inv_blinding, &leg_enc.eph_pk_auds_meds[i].0);

            t_points_r1.push(t_1);
            t_points_r2.push(t_2);
            t_points_r3.push(t_3);
            t_points_r4.push(t_4);
        }

        let amount_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        // let (asset_id_blinding_0, asset_id_blinding_1) = Self::same_blindings(rng);

        // Proving correctness of twisted Elgamal encryption of amount
        let t_amount_enc = PokPedersenCommitmentProtocol::init(
            r_3,
            r_3_blinding,
            &enc_key_gen,
            amount,
            amount_blinding,
            &enc_gen,
        );

        // Proving correctness of amount and asset-id in the commitment used with Bulletproofs
        let mut gens = bp_gens_for_vec_commitment(2, &tree_parameters.odd_parameters.bp_gens);
        let t_amount_at = SchnorrCommitment::new(
            &[
                tree_parameters.odd_parameters.pc_gens.B_blinding,
                gens.next().unwrap(),
                gens.next().unwrap(),
            ],
            vec![
                F0::rand(rng),
                amount_blinding,
                asset_id_blinding,
            ]
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

        t_comm_r_i.challenge_contribution(&mut transcript)?;

        for i in 0..asset_data.keys.len() {
            re_randomized_points[i].serialize_compressed(&mut transcript)?;
            t_points_r1[i].challenge_contribution(&mut transcript)?;
            t_points_r2[i].challenge_contribution(&leg_enc.eph_pk_auds_meds[i].0, &leg_enc.eph_pk_auds_meds[i].1, &mut transcript)?;
            t_points_r3[i].challenge_contribution(&leg_enc.eph_pk_auds_meds[i].0, &leg_enc.eph_pk_auds_meds[i].2, &mut transcript)?;
            t_points_r4[i].challenge_contribution(&leg_enc.eph_pk_auds_meds[i].0, &leg_enc.eph_pk_auds_meds[i].3, &mut transcript)?;
        }

        t_amount_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_amount,
            &mut transcript,
        )?;
        t_amount_at.challenge_contribution(
            &mut transcript,
        )?;
        t_asset_id_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_asset_id,
            &mut transcript,
        )?;

        let prover_challenge = transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        let resp_comm_r_i = t_comm_r_i.response(
            &[comm_r_i_blinding, r_1, r_2, r_3, r_4, r_2_r_1_inv, r_3_r_1_inv, r_4_r_1_inv],
            &prover_challenge
        )?;

        let mut resp_leaf_points = Vec::with_capacity(asset_data.keys.len());

        for (i, ((t_points_r2, t_points_r3), t_points_r4)) in t_points_r2.into_iter().zip(t_points_r3.into_iter()).zip(t_points_r4.into_iter()).enumerate() {
            let role = asset_data.keys[i].0;

            let mut wits1 = vec![r_1, r_1 * blindings_for_points[i]];
            if role {
                wits1.push(r_1);
            }
            let resp_1 = t_points_r1[i].response(&wits1, &prover_challenge)?;

            // TODO: Batch sigma can be used for these 3. And potentially these can be combined across keys. But then how to check the same response for r_2, r_3, r4?
            let resp_2 = t_points_r2.gen_proof(&prover_challenge);

            let resp_3 = t_points_r3.gen_proof(&prover_challenge);

            let resp_4 = t_points_r4.gen_proof(&prover_challenge);
            resp_leaf_points.push(RespLeafPoint {
                role,
                r_1: (t_points_r1[i].t, resp_1),
                r_2: resp_2,
                r_3: resp_3,
                r_4: resp_4,
            });
        }

        let resp_amount_enc = t_amount_enc.gen_proof(&prover_challenge);
        let resp_amount_at = t_amount_at.response(&[r_amount_at, amount, at], &prover_challenge)?;
        let resp_asset_id_enc = t_asset_id_enc.gen_proof(&prover_challenge);

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &tree_parameters, rng)?;

        Ok(Self {
            even_proof,
            odd_proof,
            re_randomized_path,
            resp_amount_enc,
            t_amount_at: t_amount_at.t,
            resp_amount_at,
            resp_asset_id_enc,
            // resp_asset_id,
            leaf_hat,
            split_at,
            eq_proof,
            re_randomized_points,
            comm_amount_at,
            comm_r_i,
            t_comm_r_i: t_comm_r_i.t,
            resp_comm_r_i,
            resp_leaf_points,
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
        if self.re_randomized_points.len() != self.resp_leaf_points.len() {
            return Err(Error::DifferentNumberOfRandomizedPointsAndResponses(self.re_randomized_points.len(), self.resp_leaf_points.len()))
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

        let mut vars = odd_verifier.commit_vec(2, self.comm_amount_at);
        let var_amount = vars.remove(0);
        let var_at = vars.remove(0);
        range_proof(
            &mut odd_verifier,
            var_amount.into(),
            None,
            AMOUNT_BITS.into(),
        )?;
        range_proof(
            &mut odd_verifier,
            var_at.into(),
            None,
            ASSET_ID_BITS as usize,
        )?;

        let rerandomized_leaf = self.re_randomized_path.get_rerandomized_leaf();
        debug_assert_eq!(rerandomized_leaf.into_group(), self.leaf_hat + self.split_at);

        verify_naive(
            &mut even_verifier,
            self.leaf_hat,
            self.re_randomized_points.clone(),
            &tree_parameters.odd_parameters,
        )?;

        let vars = odd_verifier.commit_vec(7, self.comm_r_i);
        crate::leg::SettlementTxnProof::<L, F0, F1, G0, G1>::enforce_constraints(&mut odd_verifier, vars);

        let mut transcript = odd_verifier.transcript();

        let comm_key1 = PedersenCommitmentKey {g: enc_gen, h: enc_key_gen};
        let comm_key2 = PedersenCommitmentKey {g: asset_comm_params.comm_key[self.re_randomized_points.len()], h: tree_parameters.even_parameters.pc_gens.B_blinding};
        self.eq_proof.verify(
            &leg_enc.ct_asset_id,
            &self.split_at,
            &comm_key1,
            &comm_key2,
            transcript
        ).unwrap();

        self.t_comm_r_i.serialize_compressed(&mut transcript)?;

        for i in 0..self.resp_leaf_points.len() {
            self.re_randomized_points[i].serialize_compressed(&mut transcript)?;
            self.resp_leaf_points[i]
                .r_1
                .0
                .serialize_compressed(&mut transcript)?;
            self.resp_leaf_points[i]
                .r_2
                .challenge_contribution(&leg_enc.eph_pk_auds_meds[i].0, &leg_enc.eph_pk_auds_meds[i].1, &mut transcript)?;
            self.resp_leaf_points[i]
                .r_3
                .challenge_contribution(&leg_enc.eph_pk_auds_meds[i].0, &leg_enc.eph_pk_auds_meds[i].2, &mut transcript)?;
            self.resp_leaf_points[i]
                .r_4
                .challenge_contribution(&leg_enc.eph_pk_auds_meds[i].0, &leg_enc.eph_pk_auds_meds[i].3, &mut transcript)?;
        }

        self.resp_amount_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_amount,
            &mut transcript,
        )?;
        self.t_amount_at.serialize_compressed(&mut transcript)?;
        self.resp_asset_id_enc.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_asset_id,
            &mut transcript,
        )?;

        let verifier_challenge = transcript.challenge_scalar::<F0>(SETTLE_TXN_CHALLENGE_LABEL);

        let mut gens = bp_gens_for_vec_commitment(2, &tree_parameters.odd_parameters.bp_gens);
        self.resp_amount_at.is_valid(
            &[
                tree_parameters.odd_parameters.pc_gens.B_blinding,
                gens.next().unwrap(),
                gens.next().unwrap(),
            ],
            &self.comm_amount_at,
            &self.t_amount_at,
            &verifier_challenge,
        )?;

        // Since challenge is different how do i make sure resp_amount_at.0[2] == eq_proof.eq[0].s1.
        // And if this isn't done then what ensures same asset id is passed to eq_proof? Just the relation
        // involving leaf_hat and split_at isn't sufficient

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

        if self.resp_amount_at.0[1] != self.resp_amount_enc.response2 {
            return Err(Error::ProofVerificationError(
                "Amount response mismatch".into(),
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

        self.resp_comm_r_i.is_valid(&crate::leg::SettlementTxnProof::<L, F0, F1, G0, G1>::bp_gens_vec(tree_parameters), &self.comm_r_i, &self.t_comm_r_i, &verifier_challenge)?;

        let aud_role_base = asset_comm_params.j_0.neg();
        let blinding_base = tree_parameters
            .odd_parameters
            .pc_gens
            .B_blinding
            .into_group()
            .neg()
            .into_affine();

        for i in 0..self.resp_leaf_points.len() {
            let resp = &self.resp_leaf_points[i];
            let role = resp.role;

            if role {
                resp.r_1.1.is_valid(
                    &[
                        self.re_randomized_points[i],
                        blinding_base,
                        aud_role_base,
                    ],
                    &leg_enc.eph_pk_auds_meds[i].0,
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
                        self.re_randomized_points[i],
                        blinding_base,
                    ],
                    &leg_enc.eph_pk_auds_meds[i].0,
                    &resp.r_1.0,
                    &verifier_challenge,
                )?;
            }

            if !resp.r_2.verify(
                &leg_enc.eph_pk_auds_meds[i].1,
                &leg_enc.eph_pk_auds_meds[i].0,
                &verifier_challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    format!("resp_leaf_points[{i}].r_2 verification mismatch"),
                ));
            }
            if !resp.r_3.verify(
                &leg_enc.eph_pk_auds_meds[i].2,
                &leg_enc.eph_pk_auds_meds[i].0,
                &verifier_challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    format!("resp_leaf_points[{i}].r_3 verification mismatch"),
                ));
            }
            if !resp.r_4.verify(
                &leg_enc.eph_pk_auds_meds[i].3,
                &leg_enc.eph_pk_auds_meds[i].0,
                &verifier_challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    format!("resp_leaf_points[{i}].r_4 verification mismatch"),
                ));
            }

            if resp.r_1.1.0[0] != self.resp_comm_r_i.0[1] {
                return Err(Error::ProofVerificationError(
                    "Mismatch in response for r_1".into(),
                ));
            }
            if resp.r_2.response != self.resp_comm_r_i.0[5] {
                return Err(Error::ProofVerificationError(
                    "Mismatch in response for r_2/r_1".into(),
                ));
            }
            if resp.r_3.response != self.resp_comm_r_i.0[6] {
                return Err(Error::ProofVerificationError(
                    "Mismatch in response for r_3/r_1".into(),
                ));
            }
            if resp.r_4.response != self.resp_comm_r_i.0[7] {
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
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::time::Instant;
    use ark_ec::VariableBaseMSM;
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::CurveTree;
    use crate::keys::{keygen_enc, keygen_sig};

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type VestaFr = ark_vesta::Fr;

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
        let asset_data = AssetData::new_alt(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        ).unwrap();

        // Check asset_data is correctly constructed
        let points = AssetData::points_alt(&asset_data.keys, &asset_comm_params);
        for i in 0..num_auditors {
            assert_eq!(
                points[i].into_group(),
                asset_comm_params.j_0 + keys_auditor[i].1.1.0
            );
        }
        for i in 0..num_mediators {
            assert_eq!(
                points[i + num_auditors].into_group(),
                keys_mediator[i].1.1.0
            );
        }

        let mut x_coords = points
            .into_iter()
            .map(|p| (asset_tree_params.odd_parameters.delta + p).into_affine().x)
            .collect::<Vec<_>>();
        x_coords.push(VestaFr::from(asset_id as u64));
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
            keys.into_iter().map(|(_, k)| k).collect(),
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
}