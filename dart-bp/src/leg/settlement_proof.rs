use crate::leg::public_asset_leg_proof::PublicAssetLegCreationProof;
use crate::leg::{
    AssetCommitmentParams, AssetData, LEG_TXN_EVEN_LABEL, LEG_TXN_ODD_LABEL, Leg, LegCreationProof,
    LegEncryption, LegEncryptionRandomness,
};
use crate::util::{
    BPProof, get_verification_tuples_with_rng, handle_verification_tuples, prove_with_rng,
};
use crate::{
    Error, LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, add_to_transcript,
    error::Result,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::string::ToString;
use ark_std::{format, vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms};
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use dock_crypto_utils::transcript::Transcript;
use rand_core::CryptoRngCore;

/// Enum representing either a hidden or revealed asset-id leg proof.
#[derive(Clone, Debug)]
pub enum LegProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// Leg proof for hidden asset-id (uses curve tree)
    HiddenAssetProof(LegCreationProof<L, F0, F1, G0, G1>),
    /// Leg proof for revealed asset-id (no curve tree)
    RevealedAssetProof(PublicAssetLegCreationProof<G0>),
}

/// Proof for a settlement involving multiple legs.
/// This allows efficient batched curve tree operations across all legs with hidden asset-ids.
///
/// * `L` - Arity
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
    /// Individual leg proofs (can be either hidden or revealed asset-id)
    pub leg_proofs: Vec<LegProof<L, F0, F1, G0, G1>>,
    /// Collection of re-randomized paths for legs with hidden asset-id in batches of size at most M.
    /// Length equals the number of HiddenAssetProof items (not total legs).
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
    ) -> Result<Self> {
        let even_transcript = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover =
            Prover::new(&tree_parameters.even_parameters.pc_gens(), even_transcript);
        let mut odd_prover = Prover::new(&tree_parameters.odd_parameters.pc_gens(), odd_transcript);

        let mut proof = Self::new_with_given_prover::<R, D0, D1, Parameters0, Parameters1>(
            rng,
            legs,
            leg_encs,
            leg_enc_rands,
            leaf_paths,
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

    /// Creates a settlement proof for multiple legs with given provers.
    /// This allows the caller to manage the provers and transcripts externally.
    ///
    /// The method uses batched curve tree operations for efficiency:
    /// - Calls `select_and_rerandomize_prover_gadget` once for all paths with hidden asset-ids
    /// - Creates each leg proof with the pre-computed rerandomized leaves (hidden asset-id legs)
    ///   or directly without curve tree (revealed asset-id legs)
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
        if num_legs != leg_encs.len() || num_legs != leg_enc_rands.len() {
            return Err(Error::ProofGenerationError(
                "Mismatched number of legs, encryptions, and randomness".to_string(),
            ));
        }

        // Count hidden asset-id legs and validate asset_data count
        let num_hidden_asset_legs = leg_encs
            .iter()
            .filter(|enc| !enc.is_asset_id_revealed())
            .count();

        if asset_data.len() != num_hidden_asset_legs {
            return Err(Error::ProofGenerationError(format!(
                "asset_data length ({}) does not match number of hidden asset-id legs ({})",
                asset_data.len(),
                num_hidden_asset_legs
            )));
        }
        let total_leaf_paths = leaf_paths
            .iter()
            .fold(0, |acc, path| acc + path.num_indices());

        if total_leaf_paths != num_hidden_asset_legs as u32 {
            return Err(Error::ProofGenerationError(format!(
                "Total number of paths in leaf_paths ({}) does not match number of hidden asset-id legs ({})",
                total_leaf_paths, num_hidden_asset_legs
            )));
        }

        add_to_transcript!(
            odd_prover.transcript(),
            ROOT_LABEL,
            asset_tree_root,
            NONCE_LABEL,
            nonce
        );

        for leg_enc in &leg_encs {
            add_to_transcript!(odd_prover.transcript(), LEG_ENC_LABEL, leg_enc,);
        }

        // Process curve tree paths for hidden asset-id legs
        let mut re_randomized_paths = Vec::with_capacity(leaf_paths.len());
        let mut all_rerandomized_leaves = Vec::with_capacity(num_hidden_asset_legs);

        for leaf_path in leaf_paths.iter() {
            let (re_randomized_path, randomizers) =
                leaf_path.batched_select_and_rerandomize_prover_gadget_new::<R, D1, D0, Parameters1, Parameters0>(
                    even_prover, odd_prover, tree_parameters, rng
                )?;

            add_to_transcript!(
                odd_prover.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );

            let rerandomized_leaves = re_randomized_path.path.get_rerandomized_leaves();
            all_rerandomized_leaves.extend(
                rerandomized_leaves
                    .into_iter()
                    .zip(randomizers)
                    .map(|(l, r)| (l, r)),
            );

            re_randomized_paths.push(re_randomized_path);
        }

        debug_assert!(all_rerandomized_leaves.len() == num_hidden_asset_legs);

        // Create individual leg proofs, based on asset-id visibility
        let mut leg_proofs = Vec::with_capacity(num_legs);
        let mut hidden_asset_idx = 0;

        for i in 0..num_legs {
            let leg_proof = if leg_encs[i].is_asset_id_revealed() {
                let proof = PublicAssetLegCreationProof::new_with_given_prover_inner(
                    rng,
                    legs[i].clone(),
                    leg_encs[i].clone(),
                    leg_enc_rands[i].clone(),
                    &tree_parameters.odd_parameters.pc_gens(),
                    &tree_parameters.odd_parameters.bp_gens(),
                    enc_key_gen,
                    enc_gen,
                    odd_prover,
                )?;
                LegProof::RevealedAssetProof(proof)
            } else {
                let (rerandomized_leaf, randomizer) = all_rerandomized_leaves[hidden_asset_idx];
                let proof = LegCreationProof::new_with_given_prover_inner::<
                    R,
                    D0,
                    Parameters0,
                    Parameters1,
                >(
                    rng,
                    legs[i].clone(),
                    leg_encs[i].clone(),
                    leg_enc_rands[i].clone(),
                    rerandomized_leaf,
                    randomizer,
                    asset_data[hidden_asset_idx].clone(),
                    tree_parameters,
                    asset_comm_params,
                    enc_key_gen,
                    enc_gen,
                    even_prover,
                    odd_prover,
                    None, // re_randomized_path is stored separately in SettlementCreationProof
                )?;

                hidden_asset_idx += 1;
                LegProof::HiddenAssetProof(proof)
            };
            leg_proofs.push(leg_proof);
        }

        Ok(Self {
            leg_proofs,
            re_randomized_paths,
            r1cs_proof: None,
        })
    }

    /// `enc_keys` and `med_keys` are the encryption (auditor) and mediator keys associated with the assets
    /// which are revealed as some leg encryptions reveal asset-id and some don't in `leg_encs`
    /// `public_enc_keys` and `public_med_keys` are the extra encryption (auditor) and mediator keys
    /// specified by leg creator and are always known to the verifier
    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        rng: &mut R,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        enc_keys: Vec<Vec<Affine<G0>>>,
        med_keys: Vec<Vec<(u8, Affine<G0>)>>, // (index in enc_keys, mediator affirmation key)
        public_enc_keys: Vec<Vec<Affine<G0>>>,
        public_med_keys: Vec<Vec<(u8, Affine<G0>)>>, // (index in public_enc_keys, mediator affirmation key)
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
                leg_encs,
                asset_tree_root,
                enc_keys,
                med_keys,
                public_enc_keys,
                public_med_keys,
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

    /// `enc_keys` and `med_keys` are the encryption (auditor) and mediator keys associated with the assets
    /// which are revealed as some leg encryptions reveal asset-id and some don't in `leg_encs`
    /// `public_enc_keys` and `public_med_keys` are the extra encryption (auditor) and mediator keys
    /// specified by leg creator and are always known to the verifier
    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        enc_keys: Vec<Vec<Affine<G0>>>,
        med_keys: Vec<Vec<(u8, Affine<G0>)>>, // (index in enc_keys, mediator affirmation key)
        public_enc_keys: Vec<Vec<Affine<G0>>>,
        public_med_keys: Vec<Vec<(u8, Affine<G0>)>>, // (index in public_enc_keys, mediator affirmation key)
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
            leg_encs,
            asset_tree_root,
            enc_keys,
            med_keys,
            public_enc_keys,
            public_med_keys,
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

    /// `enc_keys` and `med_keys` are the encryption (auditor) and mediator keys associated with the assets
    /// which are revealed as some leg encryptions reveal asset-id and some don't in `leg_encs`
    /// `public_enc_keys` and `public_med_keys` are the extra encryption (auditor) and mediator keys
    /// specified by leg creator and are always known to the verifier
    pub fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        leg_encs: Vec<LegEncryption<Affine<G0>>>,
        asset_tree_root: &Root<L, M, G1, G0>,
        enc_keys: Vec<Vec<Affine<G0>>>,
        med_keys: Vec<Vec<(u8, Affine<G0>)>>, // (index in enc_keys, mediator affirmation key)
        public_enc_keys: Vec<Vec<Affine<G0>>>,
        public_med_keys: Vec<Vec<(u8, Affine<G0>)>>, // (index in public_enc_keys, mediator affirmation key)
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

        if !public_enc_keys.is_empty() && public_enc_keys.len() != num_legs {
            return Err(Error::ProofVerificationError(format!(
                "public_enc_keys.len() must be 0 or num_legs ({}), got {}",
                num_legs,
                public_enc_keys.len()
            )));
        }
        if !public_med_keys.is_empty() && public_med_keys.len() != num_legs {
            return Err(Error::ProofVerificationError(format!(
                "public_med_keys.len() must be 0 or num_legs ({}), got {}",
                num_legs,
                public_med_keys.len()
            )));
        }

        let num_hidden_asset_legs = leg_encs
            .iter()
            .filter(|enc| !enc.is_asset_id_revealed())
            .count();
        let total_leaf_paths = self
            .re_randomized_paths
            .iter()
            .fold(0, |acc, path| acc + path.path.num_indices());

        if total_leaf_paths != num_hidden_asset_legs as u32 {
            return Err(Error::ProofVerificationError(format!(
                "Total number of paths in leaf_paths ({}) does not match number of hidden asset-id legs ({})",
                total_leaf_paths, num_hidden_asset_legs
            )));
        }

        let num_revealed_asset_legs = leg_encs.len() - num_hidden_asset_legs;
        // Ensure encryption keys and mediator keys are present for all revealed asset legs
        if num_revealed_asset_legs != enc_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "Number of encryption keys ({}) does not equal number of revealed asset-id legs ({})",
                enc_keys.len(),
                num_revealed_asset_legs
            )));
        }
        if num_revealed_asset_legs != med_keys.len() {
            return Err(Error::ProofVerificationError(format!(
                "Number of mediator key vectors ({}) does not equal number of revealed asset-id legs ({})",
                med_keys.len(),
                num_revealed_asset_legs
            )));
        }

        add_to_transcript!(
            odd_verifier.transcript(),
            ROOT_LABEL,
            asset_tree_root,
            NONCE_LABEL,
            nonce,
        );

        for leg_enc in &leg_encs {
            add_to_transcript!(odd_verifier.transcript(), LEG_ENC_LABEL, leg_enc,);
        }

        // Process curve tree paths for hidden asset-id legs
        let mut all_rerandomized_leaves = Vec::with_capacity(num_hidden_asset_legs);
        for re_randomized_path in self.re_randomized_paths.iter() {
            re_randomized_path
                .batched_select_and_rerandomize_verifier_gadget::<Parameters1, Parameters0>(
                    asset_tree_root,
                    even_verifier,
                    odd_verifier,
                    tree_parameters,
                )?;

            all_rerandomized_leaves.extend(re_randomized_path.path.get_rerandomized_leaves());

            add_to_transcript!(
                odd_verifier.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );
        }

        if all_rerandomized_leaves.len() != num_hidden_asset_legs {
            return Err(Error::ProofVerificationError(format!(
                "Number of rerandomized leaves ({}) does not match number of hidden asset-id legs ({})",
                all_rerandomized_leaves.len(),
                num_hidden_asset_legs
            )));
        }

        // Verify each leg proof based on its type
        let mut hidden_asset_idx = 0;
        let mut revealed_asset_idx = 0;

        for i in 0..num_legs {
            let leg_public_enc_keys = if public_enc_keys.is_empty() {
                vec![]
            } else {
                public_enc_keys[i].clone()
            };
            let leg_public_med_keys = if public_med_keys.is_empty() {
                vec![]
            } else {
                public_med_keys[i].clone()
            };

            match &self.leg_proofs[i] {
                LegProof::HiddenAssetProof(proof) => {
                    if leg_encs[i].is_asset_id_revealed() {
                        return Err(Error::ProofVerificationError(format!(
                            "Leg {i} is not a hidden asset-id leg"
                        )));
                    }
                    proof.verify_sigma_protocols_and_enforce_constraints_with_rerandomized_leaf::<Parameters0, Parameters1>(
                        leg_encs[i].clone(),
                        all_rerandomized_leaves[hidden_asset_idx],
                        leg_public_enc_keys,
                        leg_public_med_keys,
                        tree_parameters,
                        asset_comm_params,
                        enc_key_gen,
                        enc_gen,
                        even_verifier,
                        odd_verifier,
                        rmc.as_deref_mut(),
                    )?;

                    hidden_asset_idx += 1;
                }
                LegProof::RevealedAssetProof(proof) => {
                    if !leg_encs[i].is_asset_id_revealed() {
                        return Err(Error::ProofVerificationError(format!(
                            "Leg {i} is not a revealed asset-id leg"
                        )));
                    }

                    proof.verify_sigma_protocols_and_enforce_constraints_inner(
                        leg_encs[i].clone(),
                        enc_keys[revealed_asset_idx].clone(),
                        med_keys[revealed_asset_idx].clone(),
                        leg_public_enc_keys,
                        leg_public_med_keys,
                        &tree_parameters.odd_parameters.pc_gens(),
                        &tree_parameters.odd_parameters.bp_gens(),
                        enc_key_gen,
                        enc_gen,
                        odd_verifier,
                        rmc.as_deref_mut(),
                    )?;
                    revealed_asset_idx += 1;
                }
            }
        }

        Ok(())
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CanonicalSerialize for LegProof<L, F0, F1, G0, G1>
{
    fn serialize_with_mode<W: ark_std::io::Write>(
        &self,
        mut writer: W,
        compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        match self {
            LegProof::HiddenAssetProof(proof) => {
                0u8.serialize_with_mode(&mut writer, compress)?;
                proof.serialize_with_mode(&mut writer, compress)
            }
            LegProof::RevealedAssetProof(proof) => {
                1u8.serialize_with_mode(&mut writer, compress)?;
                proof.serialize_with_mode(&mut writer, compress)
            }
        }
    }

    fn serialized_size(&self, compress: ark_serialize::Compress) -> usize {
        1 + match self {
            LegProof::HiddenAssetProof(proof) => proof.serialized_size(compress),
            LegProof::RevealedAssetProof(proof) => proof.serialized_size(compress),
        }
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CanonicalDeserialize for LegProof<L, F0, F1, G0, G1>
{
    fn deserialize_with_mode<R: ark_std::io::Read>(
        mut reader: R,
        compress: ark_serialize::Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        let discriminant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
        match discriminant {
            0 => Ok(LegProof::HiddenAssetProof(
                LegCreationProof::deserialize_with_mode(&mut reader, compress, validate)?,
            )),
            1 => Ok(LegProof::RevealedAssetProof(
                PublicAssetLegCreationProof::deserialize_with_mode(
                    &mut reader,
                    compress,
                    validate,
                )?,
            )),
            _ => Err(ark_serialize::SerializationError::InvalidData),
        }
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> ark_serialize::Valid for LegProof<L, F0, F1, G0, G1>
{
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        match self {
            LegProof::HiddenAssetProof(proof) => proof.check(),
            LegProof::RevealedAssetProof(proof) => proof.check(),
        }
    }
}
