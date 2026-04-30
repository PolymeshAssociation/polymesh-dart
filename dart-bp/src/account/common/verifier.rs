use crate::account::common::balance::BalanceChangeProof;
use crate::account::common::balance::BalanceChangeSplitProof;
use crate::account::common::leg_link::{LegAccountLink, LegVerifierConfig};
use crate::account::state::{
    ASSET_ID_GEN_INDEX, BALANCE_GEN_INDEX, COUNTER_GEN_INDEX, CURRENT_RANDOMNESS_GEN_INDEX,
    CURRENT_RHO_GEN_INDEX, ID_GEN_INDEX, NUM_GENERATORS, RANDOMNESS_GEN_INDEX, RHO_GEN_INDEX,
};
use crate::account::{
    AccountCommitmentKeyTrait, AccountStateCommitment, AmountCiphertext, CommonStateChangeProof,
};
use crate::util::{
    bp_gens_vec_for_randomness_relations, enforce_balance_change_verifier,
    enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change,
    enforce_constraints_for_randomness_relations, get_verification_tuples_with_rng,
    handle_verification_tuples, take_challenge_contrib_of_sigma_t_values_for_balance_change,
    verify_sigma_for_balance_change, verify_sigma_for_common_state_change,
};
use crate::{
    Error, LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_EVEN_LABEL,
    TXN_ODD_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript, error::Result,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use ark_std::collections::BTreeMap;
use ark_std::format;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use bulletproofs::r1cs::{ConstraintSystem, VerificationTuple, Verifier};
use curve_tree_relations::curve_tree::Root;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use dock_crypto_utils::transcript::Transcript;
use rand_core::CryptoRngCore;

use super::CommonAffirmationSplitProof;

pub struct StateChangeVerifier<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// When these 2 are None, external `Verifier`s are being used and `StateChangeVerifier` only
    /// verifies the sigma protocols and enforces the Bulletproof constraints.
    pub even_verifier: Option<Verifier<MerlinTranscript, Affine<G0>>>,
    pub odd_verifier: Option<Verifier<MerlinTranscript, Affine<G1>>>,
    pub re_randomized_leaf: Affine<G0>,
    pub legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> StateChangeVerifier<L, F0, F1, G0, G1>
{
    /// Takes challenge contributions from all relevant subprotocols
    /// `has_balance_decreased` is None when balance doesn't change
    /// `has_counter_decreased` is None when counter doesn't change
    pub fn init<Parameters0: DiscreteLogParameters, Parameters1: DiscreteLogParameters>(
        proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        let mut verifier = Self::init_with_given_verifier(
            proof,
            legs_with_conf,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
        )?;
        verifier.even_verifier = Some(even_verifier);
        verifier.odd_verifier = Some(odd_verifier);
        Ok(verifier)
    }

    /// Enforce Bulletproofs constraints for balance change and takes challenge contributions from balance change related subprotocols
    pub fn init_balance_change_verification(
        &mut self,
        proof: &BalanceChangeProof<F0, G0>,
        ct_amounts: &[AmountCiphertext<Affine<G0>>],
        enc_gen: Affine<G0>,
    ) -> Result<()> {
        let mut even_verifier = self.even_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError(
                "even_verifier is missing or already consumed; use init() or init_with_given_verifier*"
                    .to_string(),
            )
        })?;
        self.init_balance_change_verification_with_given_verifier(
            proof,
            ct_amounts,
            enc_gen,
            &mut even_verifier,
        )?;
        self.even_verifier = Some(even_verifier);
        Ok(())
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        rng: &mut R,
        common_state_change_proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        balance_change_proof: Option<&BalanceChangeProof<F0, G0>>,
        challenge: &F0,
        ct_amounts: Vec<AmountCiphertext<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };

        let (even_tuple, odd_tuple) = self.verify_sigma_protocols_and_return_tuples(
            common_state_change_proof,
            balance_change_proof,
            challenge,
            ct_amounts,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rng,
            rmc_0,
        )?;

        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_sigma_protocols_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        mut self,
        common_state_change_proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        balance_change_proof: Option<&BalanceChangeProof<F0, G0>>,
        challenge: &F0,
        ct_amounts: Vec<AmountCiphertext<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_verifier = self.even_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError(
                "even_verifier is missing or already consumed".to_string(),
            )
        })?;
        let odd_verifier = self.odd_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError("odd_verifier is missing or already consumed".to_string())
        })?;

        self.verify_sigma_protocols(
            common_state_change_proof,
            balance_change_proof,
            challenge,
            ct_amounts,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rmc,
        )?;

        let r1cs_proof = common_state_change_proof
            .partial
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

    pub fn init_with_given_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
    ) -> Result<Self> {
        let re_randomized_path = proof.partial.re_randomized_path.as_ref().ok_or_else(|| {
            Error::ProofVerificationError(
                "re_randomized_path is None, use batched verification instead".to_string(),
            )
        })?;
        re_randomized_path.select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
            root,
            even_verifier,
            odd_verifier,
            account_tree_params,
        )?;
        let re_randomized_leaf = re_randomized_path.path.get_rerandomized_leaf();

        add_to_transcript!(
            even_verifier.transcript(),
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
        );

        Self::init_with_given_verifier_with_rerandomized_leaf(
            proof,
            legs_with_conf,
            updated_account_commitment,
            nullifier,
            re_randomized_leaf,
            nonce,
            account_comm_key,
            enc_gen,
            even_verifier,
        )
    }

    /// Initializes verifier when the leaf has already been re-randomized externally.
    /// This is useful for batched verification when verifying multiple paths at once.
    /// `rerandomized_leaf` - The re-randomized leaf obtained from external curve tree operations.
    pub fn init_with_given_verifier_with_rerandomized_leaf(
        proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        re_randomized_leaf: Affine<G0>,
        nonce: &[u8],
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    ) -> Result<Self> {
        if legs_with_conf.is_empty() {
            return Err(Error::ProofVerificationError(
                "No legs added to the verifier".to_string(),
            ));
        }
        if legs_with_conf.len() != proof.resp_leg_link.len() {
            return Err(Error::ProofVerificationError(format!(
                "Needed {} leg proofs but got {}",
                legs_with_conf.len(),
                proof.resp_leg_link.len()
            )));
        }

        let mut asset_id = None;
        for (i, leg_conf) in legs_with_conf.iter().enumerate() {
            if asset_id.is_none() {
                asset_id = leg_conf.encryption.asset_id();
            } else if leg_conf.encryption.is_asset_id_revealed()
                && (asset_id != leg_conf.encryption.asset_id())
            {
                return Err(Error::ProofVerificationError(
                    "All legs must have the same asset id".to_string(),
                ));
            }

            if !leg_conf.encryption.is_asset_id_revealed() {
                if matches!(
                    proof.resp_leg_link[i],
                    LegAccountLink::AssetIdRevealed {
                        resp_participant: _
                    }
                ) {
                    return Err(Error::ProofVerificationError(format!(
                        "Leg {i} has a hidden asset_id but auth proof marks it as revealed"
                    )));
                }
            }
        }

        // If asset-id is revealed, there would be one less response
        let expected_num_resps = NUM_GENERATORS + { asset_id.is_none() as usize };
        if proof.resp_acc_old.len() != expected_num_resps {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                expected_num_resps,
                proof.resp_acc_old.len(),
            ));
        }

        let has_balance_changed = legs_with_conf
            .iter()
            .any(|l| l.has_balance_decreased.is_some());
        let expected_num_resps = 2 + has_balance_changed as usize;
        if proof.resp_acc_new.responses.len() != expected_num_resps {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                expected_num_resps,
                proof.resp_acc_new.responses.len(),
            ));
        }

        // sk_enc and sk_enc^{-1} relation is always proved in BP (regardless of asset-id revealed or not).
        // resp_bp_randomness_relations always has 2 responses: blinding for comm_bp and sk_enc_inv (positions 0 and 8).
        let expected_num_resps = 2;
        if proof.partial.resp_bp_randomness_relations.responses.len() != expected_num_resps {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                expected_num_resps,
                proof.partial.resp_bp_randomness_relations.responses.len(),
            ));
        }

        add_to_transcript!(
            even_verifier.transcript(),
            NONCE_LABEL,
            nonce,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        for leg_conf in &legs_with_conf {
            add_to_transcript!(
                even_verifier.transcript(),
                LEG_ENC_LABEL,
                leg_conf.encryption,
                LEG_ENC_LABEL,
                leg_conf.party_eph_pk
            );
        }

        enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change(
            legs_with_conf
                .iter()
                .map(|l| (l.encryption.clone(), l.party_eph_pk.clone()))
                .collect(),
            asset_id,
            &nullifier,
            proof.partial.comm_bp_randomness_relations,
            &proof.t_acc_old,
            &proof.t_acc_new,
            &proof.partial.t_bp_randomness_relations,
            &proof.partial.resp_null,
            &proof.resp_leg_link,
            even_verifier,
            account_comm_key,
            enc_gen,
        )?;
        // External `Verifier`s will be used to verify this
        Ok(Self {
            even_verifier: None,
            odd_verifier: None,
            re_randomized_leaf,
            legs_with_conf,
        })
    }

    pub fn init_balance_change_verification_with_given_verifier(
        &mut self,
        proof: &BalanceChangeProof<F0, G0>,
        ct_amounts: &[AmountCiphertext<Affine<G0>>],
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    ) -> Result<()> {
        let has_balance_decreased: Vec<bool> = self
            .legs_with_conf
            .iter()
            .filter_map(|l| l.has_balance_decreased)
            .collect();
        if has_balance_decreased.is_empty() {
            return Err(Error::ProofVerificationError("`has_balance_decreased` wasn't set but still trying to take challenge contribution".into()));
        }
        enforce_balance_change_verifier(
            proof.partial.comm_bp_bal,
            has_balance_decreased,
            even_verifier,
        )?;

        let mut verifier_transcript = even_verifier.transcript();

        take_challenge_contrib_of_sigma_t_values_for_balance_change(
            ct_amounts,
            &proof.partial.t_comm_bp_bal,
            &proof.resp_leg_amount,
            enc_gen,
            &mut verifier_transcript,
        )?;
        Ok(())
    }

    pub fn verify_sigma_protocols<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        common_state_change_proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        balance_change_proof: Option<&BalanceChangeProof<F0, G0>>,
        challenge: &F0,
        ct_amounts: Vec<AmountCiphertext<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let pc_gens = account_tree_params.even_parameters.pc_gens();
        let bp_gens = account_tree_params.even_parameters.bp_gens();

        let leg_cores: Vec<_> = self
            .legs_with_conf
            .iter()
            .map(|l| (l.encryption.clone(), l.party_eph_pk.clone()))
            .collect();
        let has_counter_decreased: Vec<Option<bool>> = self
            .legs_with_conf
            .iter()
            .map(|l| l.has_counter_decreased)
            .collect();
        let _ = verify_sigma_for_common_state_change(
            &leg_cores,
            has_counter_decreased,
            balance_change_proof.is_some(),
            &nullifier,
            &self.re_randomized_leaf,
            &updated_account_commitment.0,
            &common_state_change_proof
                .partial
                .comm_bp_randomness_relations,
            &common_state_change_proof.t_acc_old,
            &common_state_change_proof.t_acc_new,
            &common_state_change_proof.partial.t_bp_randomness_relations,
            &common_state_change_proof.resp_acc_old,
            &common_state_change_proof.resp_acc_new,
            &common_state_change_proof.partial.resp_null,
            &common_state_change_proof.resp_leg_link,
            &common_state_change_proof
                .partial
                .resp_bp_randomness_relations,
            &challenge,
            account_comm_key,
            pc_gens,
            bp_gens,
            enc_gen,
            rmc.as_deref_mut(),
        )?;

        if let Some(balance_change_proof) = balance_change_proof {
            // Filter legs to only include legs with balance changes
            let balance_ct_amounts: Vec<AmountCiphertext<Affine<G0>>> = ct_amounts
                .into_iter()
                .zip(self.legs_with_conf.iter())
                .filter(|(_, leg)| leg.has_balance_decreased.is_some())
                .map(|(ct, _)| ct)
                .collect();

            verify_sigma_for_balance_change(
                &balance_ct_amounts,
                &balance_change_proof.resp_leg_amount,
                &balance_change_proof.partial.comm_bp_bal,
                &balance_change_proof.partial.t_comm_bp_bal,
                &balance_change_proof.partial.resp_comm_bp_bal,
                &challenge,
                *common_state_change_proof
                    .resp_acc_old
                    .0
                    .get(BALANCE_GEN_INDEX)
                    .ok_or_else(|| {
                        Error::ProofVerificationError(format!(
                            "Missing resp_leaf response at BALANCE_GEN_INDEX={BALANCE_GEN_INDEX}"
                        ))
                    })?,
                *common_state_change_proof
                    .resp_acc_new
                    .responses
                    .get(&BALANCE_GEN_INDEX)
                    .ok_or_else(|| {
                        Error::ProofVerificationError(format!(
                            "Missing resp_acc_new response for BALANCE_GEN_INDEX={BALANCE_GEN_INDEX}"
                        ))
                    })?,
                *common_state_change_proof.partial
                    .resp_bp_randomness_relations
                    .responses
                    .get(&8)
                    .ok_or_else(|| {
                        Error::ProofVerificationError(
                            "Missing resp_bp response for sk_enc_inv (index 8)".to_string(),
                        )
                    })?, // sk_enc_inv from resp_bp position 8 (always present)
                pc_gens,
                bp_gens,
                enc_gen,
                rmc.as_deref_mut(),
            )?;
        }
        Ok(())
    }
}

/// Verifier for split (host/auth) affirmation proofs.
/// Mirrors `StateChangeVerifier` but operates on `CommonAffirmationSplitProof` and `BalanceChangeSplitProof`.
pub struct SplitStateChangeVerifier<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_verifier: Option<Verifier<MerlinTranscript, Affine<G0>>>,
    pub odd_verifier: Option<Verifier<MerlinTranscript, Affine<G1>>>,
    pub re_randomized_leaf: Affine<G0>,
    pub legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SplitStateChangeVerifier<L, F0, F1, G0, G1>
{
    /// Set up BP constraints and challenge contributions for the common (non-balance) part.
    pub fn init<Parameters0: DiscreteLogParameters, Parameters1: DiscreteLogParameters>(
        proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

        let mut verifier = Self::init_with_given_verifier::<Parameters0, Parameters1>(
            proof,
            legs_with_conf,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
        )?;
        verifier.even_verifier = Some(even_verifier);
        verifier.odd_verifier = Some(odd_verifier);
        Ok(verifier)
    }

    pub fn init_with_given_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
    ) -> Result<Self> {
        let re_randomized_path = proof.partial.re_randomized_path.as_ref().ok_or_else(|| {
            Error::ProofVerificationError(
                "re_randomized_path is None, use batched verification instead".to_string(),
            )
        })?;

        // Curve-tree verifier gadget
        re_randomized_path.select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
            root,
            even_verifier,
            odd_verifier,
            account_tree_params,
        )?;

        let re_randomized_leaf = re_randomized_path.path.get_rerandomized_leaf();

        // Public inputs to transcript
        add_to_transcript!(
            even_verifier.transcript(),
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
        );

        let B_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

        Self::init_with_given_verifier_with_rerandomized_leaf(
            proof,
            legs_with_conf,
            updated_account_commitment,
            nullifier,
            re_randomized_leaf,
            nonce,
            account_comm_key,
            enc_gen,
            B_blinding,
            even_verifier,
        )
    }

    /// Initialize when the leaf has already been re-randomized externally (batched multi-asset).
    /// Skips curve-tree gadget. Takes rerandomized leaf directly and only even_verifier.
    pub fn init_with_given_verifier_with_rerandomized_leaf(
        proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        legs_with_conf: Vec<LegVerifierConfig<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        re_randomized_leaf: Affine<G0>,
        nonce: &[u8],
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        B_blinding: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    ) -> Result<Self> {
        // NOTE: No curve-tree gadget or ROOT/RE_RANDOMIZED_PATH transcript entries.
        // Those are handled externally by the batched multi-asset verifier.

        let is_asset_id_revealed = LegVerifierConfig::is_asset_id_revealed_in_any(&legs_with_conf);

        let num_hidden_asset_ids = LegVerifierConfig::num_hidden_asset_ids(&legs_with_conf);

        if proof.auth_proof.partial_ct_asset_ids.len() != num_hidden_asset_ids {
            return Err(Error::ProofVerificationError(format!(
                "Invalid proof.auth_proof.partial_ct_asset_ids length. Expected {}, got {}",
                num_hidden_asset_ids,
                proof.auth_proof.partial_ct_asset_ids.len()
            )));
        }

        if proof.resp_ct_asset_id.len() != num_hidden_asset_ids {
            return Err(Error::ProofVerificationError(format!(
                "Invalid proof.resp_ct_asset_id length. Expected {}, got {}",
                num_hidden_asset_ids,
                proof.resp_ct_asset_id.len()
            )));
        }

        let expected_host_comm_resp_len = if is_asset_id_revealed {
            NUM_GENERATORS - 2
        } else {
            NUM_GENERATORS - 1
        };

        if proof.host_commitment_proof.resp_acc_old.0.len() != expected_host_comm_resp_len {
            return Err(Error::ProofVerificationError(format!(
                "Invalid host commitment resp_acc_old length. Expected {}, got {}",
                expected_host_comm_resp_len,
                proof.host_commitment_proof.resp_acc_old.0.len()
            )));
        }

        add_to_transcript!(
            even_verifier.transcript(),
            NONCE_LABEL,
            nonce,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        // Leg data to transcript
        for leg_conf in &legs_with_conf {
            add_to_transcript!(
                even_verifier.transcript(),
                LEG_ENC_LABEL,
                leg_conf.encryption,
                LEG_ENC_LABEL,
                leg_conf.party_eph_pk
            );
        }

        // BP constraints: commit_vec(6, comm_bp) + enforce_constraints_for_randomness_relations
        let mut vars = even_verifier.commit_vec(6, proof.partial.comm_bp_randomness_relations);
        enforce_constraints_for_randomness_relations(even_verifier, &mut vars);

        // Challenge contributions: host commitment, BP/null
        {
            let mut transcript = even_verifier.transcript();
            proof
                .host_commitment_proof
                .challenge_contribution(&mut transcript)?;
            proof
                .partial
                .t_bp_randomness_relations
                .serialize_compressed(&mut transcript)?;
            let null_gen = account_comm_key.current_rho_gen();
            proof.partial.resp_null.challenge_contribution(
                &null_gen,
                &nullifier,
                &mut transcript,
            )?;
        }

        // ct_asset_id_2 challenge contributions
        if !is_asset_id_revealed {
            let mut transcript = even_verifier.transcript();
            let mut asset_id_idx = 0;
            for leg_conf in &legs_with_conf {
                if !leg_conf.encryption.is_asset_id_revealed() {
                    let ct_asset_id =
                        leg_conf.encryption.asset_id_ciphertext().ok_or_else(|| {
                            Error::ProofVerificationError(
                                "ct_asset_id missing for leg with hidden asset-id".to_string(),
                            )
                        })?;
                    let ct_asset_id_1 = proof.auth_proof.partial_ct_asset_ids[asset_id_idx];
                    let ct_asset_id_2 =
                        (ct_asset_id.into_group() - ct_asset_id_1.into_group()).into_affine();
                    proof.resp_ct_asset_id[asset_id_idx].challenge_contribution(
                        &enc_gen,
                        &B_blinding,
                        &ct_asset_id_2,
                        &mut transcript,
                    )?;
                    asset_id_idx += 1;
                }
            }
        }

        {
            let (y_old, y_new) = old_and_new_host_commitments(
                proof,
                re_randomized_leaf,
                updated_account_commitment,
                &legs_with_conf,
                account_comm_key,
            )?;

            let mut transcript = even_verifier.transcript();
            y_old.serialize_compressed(&mut transcript)?;
            y_new.serialize_compressed(&mut transcript)?;
        }

        Ok(Self {
            even_verifier: None,
            odd_verifier: None,
            re_randomized_leaf,
            legs_with_conf,
        })
    }

    /// Enforce Bulletproofs constraints for balance change and add balance challenge contributions.
    pub fn init_balance_change_verification(
        &mut self,
        common_proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        balance_proof: &BalanceChangeSplitProof<F0, G0>,
        enc_gen: Affine<G0>,
        account_tree_params_pc_gens_B_blinding: Affine<G0>,
    ) -> Result<()> {
        let mut even_verifier = self.even_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError(
                "even_verifier is missing or already consumed; use init()".to_string(),
            )
        })?;
        self.init_balance_change_verification_with_given_verifier(
            common_proof,
            balance_proof,
            enc_gen,
            account_tree_params_pc_gens_B_blinding,
            &mut even_verifier,
        )?;
        self.even_verifier = Some(even_verifier);
        Ok(())
    }

    pub fn init_balance_change_verification_with_given_verifier(
        &mut self,
        common_proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        balance_proof: &BalanceChangeSplitProof<F0, G0>,
        enc_gen: Affine<G0>,
        B_blinding: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    ) -> Result<()> {
        let has_decreased: Vec<bool> = self
            .legs_with_conf
            .iter()
            .filter_map(|l| l.has_balance_decreased)
            .collect();

        let num_balance_decreases = has_decreased.len();

        if common_proof.auth_proof.partial_ct_amounts.len() != num_balance_decreases {
            return Err(Error::ProofVerificationError(format!(
                "Invalid common_proof.auth_proof.partial_ct_amounts length. Expected {}, got {}",
                num_balance_decreases,
                common_proof.auth_proof.partial_ct_amounts.len()
            )));
        }

        if balance_proof.resp_ct_amount.len() != num_balance_decreases {
            return Err(Error::ProofVerificationError(format!(
                "Invalid balance_proof.resp_ct_amount length. Expected {}, got {}",
                num_balance_decreases,
                balance_proof.resp_ct_amount.len()
            )));
        }

        let expected_resp_acc_new_len = 3 + if num_balance_decreases > 0 { 1 } else { 0 };
        if common_proof
            .host_commitment_proof
            .resp_acc_new
            .responses
            .len()
            != expected_resp_acc_new_len
        {
            return Err(Error::ProofVerificationError(format!(
                "Invalid host commitment resp_acc_new length. Expected {}, got {}",
                expected_resp_acc_new_len,
                common_proof
                    .host_commitment_proof
                    .resp_acc_new
                    .responses
                    .len()
            )));
        }

        enforce_balance_change_verifier(
            balance_proof.partial.comm_bp_bal,
            has_decreased,
            even_verifier,
        )?;

        // Balance T-value and ct_amount_2 challenge contributions
        {
            let mut transcript = even_verifier.transcript();

            balance_proof
                .partial
                .t_comm_bp_bal
                .serialize_compressed(&mut transcript)?;

            let mut amount_idx = 0;
            for leg_conf in &self.legs_with_conf {
                if leg_conf.has_balance_decreased.is_some() {
                    let ct_amount = leg_conf.encryption.ct_amount;
                    let ct_amount_1 = common_proof.auth_proof.partial_ct_amounts[amount_idx];
                    let ct_amount_2 =
                        (ct_amount.into_group() - ct_amount_1.into_group()).into_affine();
                    balance_proof.resp_ct_amount[amount_idx].challenge_contribution(
                        &enc_gen,
                        &B_blinding,
                        &ct_amount_2,
                        &mut transcript,
                    )?;
                    amount_idx += 1;
                }
            }
        }

        Ok(())
    }

    /// Verify all sigma protocols and return verification tuples for deferred R1CS verification.
    /// Does not verify auth proof.
    pub fn verify_sigma_protocols_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        mut self,
        common_proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        balance_proof: Option<&BalanceChangeSplitProof<F0, G0>>,
        challenge: &F0,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_verifier = self.even_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError(
                "even_verifier is missing or already consumed".to_string(),
            )
        })?;
        let odd_verifier = self.odd_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError("odd_verifier is missing or already consumed".to_string())
        })?;

        self.verify_sigma_protocols(
            common_proof,
            balance_proof,
            challenge,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rmc.as_deref_mut(),
        )?;

        let r1cs_proof =
            common_proof.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )
    }

    /// Does not verify sigma protocols of auth proof.
    pub fn verify_sigma_protocols<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        common_proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        balance_proof: Option<&BalanceChangeSplitProof<F0, G0>>,
        challenge: &F0,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let is_asset_id_revealed =
            LegVerifierConfig::is_asset_id_revealed_in_any(&self.legs_with_conf);
        let has_balance_changed = LegVerifierConfig::has_balance_changed(&self.legs_with_conf);
        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        let (y_old, y_new) = old_and_new_host_commitments(
            common_proof,
            self.re_randomized_leaf,
            updated_account_commitment,
            &self.legs_with_conf,
            account_comm_key,
        )?;

        let (gens_acc_old, gens_acc_new): (Vec<Affine<G0>>, Vec<Affine<G0>>) =
            if is_asset_id_revealed {
                let mut new_gens = account_comm_key.as_gens_without_sk_and_asset_id().to_vec();
                new_gens.push(b_blinding);
                (
                    account_comm_key
                        .as_gens_with_blinding_without_sk_and_asset_id(b_blinding)
                        .to_vec(),
                    new_gens,
                )
            } else {
                let mut new_gens = account_comm_key.as_gens_without_sk().to_vec();
                new_gens.push(b_blinding);
                (
                    account_comm_key
                        .as_gens_with_blinding_without_sk(b_blinding)
                        .to_vec(),
                    new_gens,
                )
            };

        verify_schnorr_resp_or_rmc!(
            rmc,
            common_proof.host_commitment_proof.resp_acc_old,
            gens_acc_old,
            y_old,
            common_proof.host_commitment_proof.t_acc_old,
            challenge,
        );

        let mut missing_resps_acc_new = BTreeMap::new();
        // for i in 0..gens_acc_new.len() {
        //     if i == idx_current_rho || i == idx_current_randomness {
        //         continue;
        //     }
        //     if i == idx_b_blinding_new {
        //         continue;
        //     }
        //     if has_balance_changed && i == 0 {
        //         continue;
        //     }
        //     missing_resps_acc_new.insert(i, common_proof.host_commitment_proof.resp_acc_old.0[i]);
        // }

        // -1 as sk is not present
        if !has_balance_changed {
            missing_resps_acc_new.insert(
                BALANCE_GEN_INDEX - 1,
                common_proof.host_commitment_proof.resp_acc_old.0[BALANCE_GEN_INDEX - 1],
            );
        }
        missing_resps_acc_new.insert(
            COUNTER_GEN_INDEX - 1,
            common_proof.host_commitment_proof.resp_acc_old.0[COUNTER_GEN_INDEX - 1],
        );

        if !is_asset_id_revealed {
            missing_resps_acc_new.insert(
                ASSET_ID_GEN_INDEX - 1,
                common_proof.host_commitment_proof.resp_acc_old.0[ASSET_ID_GEN_INDEX - 1],
            );
        }

        let offset = if is_asset_id_revealed { 1 } else { 0 };
        // Since response for asset id is not present when revealed, adjust indices of remaining responses accordingly
        missing_resps_acc_new.insert(
            RHO_GEN_INDEX - offset - 1,
            common_proof.host_commitment_proof.resp_acc_old.0[RHO_GEN_INDEX - offset - 1],
        );
        missing_resps_acc_new.insert(
            RANDOMNESS_GEN_INDEX - offset - 1,
            common_proof.host_commitment_proof.resp_acc_old.0[RANDOMNESS_GEN_INDEX - offset - 1],
        );
        missing_resps_acc_new.insert(
            ID_GEN_INDEX - offset - 1,
            common_proof.host_commitment_proof.resp_acc_old.0[ID_GEN_INDEX - offset - 1],
        );

        verify_partial_schnorr_resp_or_rmc!(
            rmc,
            common_proof.host_commitment_proof.resp_acc_new,
            gens_acc_new,
            y_new,
            common_proof.host_commitment_proof.t_acc_new,
            challenge,
            missing_resps_acc_new,
        );

        // Verify BP/null sigma protocols
        let resp_new_current_rho = common_proof
            .host_commitment_proof
            .resp_acc_new
            .responses
            .get(&(CURRENT_RHO_GEN_INDEX - offset - 1))
            .copied()
            .ok_or_else(|| {
                Error::ProofVerificationError(
                    "Missing resp_acc_new response for current_rho".to_string(),
                )
            })?;

        let resp_new_current_randomness = common_proof
            .host_commitment_proof
            .resp_acc_new
            .responses
            .get(&(CURRENT_RANDOMNESS_GEN_INDEX - offset - 1))
            .copied()
            .ok_or_else(|| {
                Error::ProofVerificationError(
                    "Missing resp_acc_new response for current_randomness".to_string(),
                )
            })?;

        let mut missing_resps_bp = BTreeMap::new();
        missing_resps_bp.insert(
            1,
            common_proof.host_commitment_proof.resp_acc_old.0[RHO_GEN_INDEX - offset - 1],
        );
        missing_resps_bp.insert(
            2,
            common_proof.host_commitment_proof.resp_acc_old.0[CURRENT_RHO_GEN_INDEX - offset - 1],
        );
        missing_resps_bp.insert(3, resp_new_current_rho);
        missing_resps_bp.insert(
            4,
            common_proof.host_commitment_proof.resp_acc_old.0[RANDOMNESS_GEN_INDEX - offset - 1],
        );
        missing_resps_bp.insert(
            5,
            common_proof.host_commitment_proof.resp_acc_old.0
                [CURRENT_RANDOMNESS_GEN_INDEX - offset - 1],
        );
        missing_resps_bp.insert(6, resp_new_current_randomness);

        let nullifier_gen = account_comm_key.current_rho_gen();

        verify_or_rmc_2!(
            rmc,
            common_proof.partial.resp_null,
            "Nullifier proof verification failed",
            nullifier,
            nullifier_gen,
            challenge,
            &common_proof.host_commitment_proof.resp_acc_old.0[CURRENT_RHO_GEN_INDEX - offset - 1],
        );

        let bp_gens_vec = bp_gens_vec_for_randomness_relations(
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
        )
        .to_vec();

        verify_partial_schnorr_resp_or_rmc!(
            rmc,
            common_proof.partial.resp_bp_randomness_relations,
            bp_gens_vec,
            common_proof.partial.comm_bp_randomness_relations,
            common_proof.partial.t_bp_randomness_relations,
            challenge,
            missing_resps_bp,
        );

        // Verify balance partial proof (if applicable)
        if let Some(balance_proof) = balance_proof {
            let num_amounts = balance_proof.resp_ct_amount.len();

            let mut gens_iter = crate::util::bp_gens_for_vec_commitment(
                2 + num_amounts as u32,
                &account_tree_params.even_parameters.bp_gens(),
            );
            let mut bp_bal_gens = Vec::with_capacity(3 + num_amounts);
            bp_bal_gens.push(account_tree_params.even_parameters.pc_gens().B_blinding);
            for _ in 0..2 + num_amounts {
                bp_bal_gens.push(gens_iter.next().unwrap());
            }

            let resp_old_bal = common_proof.host_commitment_proof.resp_acc_old.0[0];
            let resp_new_bal = if has_balance_changed {
                *common_proof
                    .host_commitment_proof
                    .resp_acc_new
                    .responses
                    .get(&0)
                    .ok_or_else(|| {
                        Error::ProofVerificationError(
                            "Missing resp_acc_new response for balance (index 0)".to_string(),
                        )
                    })?
            } else {
                resp_old_bal
            };

            let mut missing_resps_bal = BTreeMap::new();
            missing_resps_bal.insert(1 + num_amounts, resp_old_bal);
            missing_resps_bal.insert(1 + num_amounts + 1, resp_new_bal);

            verify_partial_schnorr_resp_or_rmc!(
                rmc,
                balance_proof.partial.resp_comm_bp_bal,
                bp_bal_gens,
                balance_proof.partial.comm_bp_bal,
                balance_proof.partial.t_comm_bp_bal,
                challenge,
                missing_resps_bal,
            );

            // Verify ct_amount_2 PokPedersenCommitment proofs
            let B_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
            let mut amount_idx = 0;
            for leg_conf in &self.legs_with_conf {
                if leg_conf.has_balance_decreased.is_some() {
                    let ct_amount = leg_conf.encryption.ct_amount;
                    let ct_amount_1 = common_proof.auth_proof.partial_ct_amounts[amount_idx];
                    let ct_amount_2 =
                        (ct_amount.into_group() - ct_amount_1.into_group()).into_affine();

                    verify_or_rmc_3!(
                        rmc,
                        balance_proof.resp_ct_amount[amount_idx],
                        format!("ct_amount_2 verification failed for leg {amount_idx}"),
                        ct_amount_2,
                        enc_gen,
                        B_blinding,
                        challenge,
                    );
                    amount_idx += 1;
                }
            }
        }

        // Verify ct_asset_id_2 PokPedersenCommitment proofs
        if !is_asset_id_revealed {
            let B_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
            let mut asset_id_idx = 0;
            for leg_conf in &self.legs_with_conf {
                if !leg_conf.encryption.is_asset_id_revealed() {
                    let ct_asset_id =
                        leg_conf.encryption.asset_id_ciphertext().ok_or_else(|| {
                            Error::ProofVerificationError(
                                "ct_asset_id missing for leg with hidden asset-id".to_string(),
                            )
                        })?;
                    let ct_asset_id_1 = common_proof.auth_proof.partial_ct_asset_ids[asset_id_idx];
                    let ct_asset_id_2 =
                        (ct_asset_id.into_group() - ct_asset_id_1.into_group()).into_affine();

                    verify_or_rmc_3!(
                        rmc,
                        common_proof.resp_ct_asset_id[asset_id_idx],
                        format!("ct_asset_id_2 verification failed for leg {asset_id_idx}"),
                        ct_asset_id_2,
                        enc_gen,
                        B_blinding,
                        challenge,
                    );
                    asset_id_idx += 1;
                }
            }
        }

        Ok(())
    }

    /// Sigma protocols, R1CS, and handle tuples — given an externally-derived challenge. Mirrors `StateChangeVerifier::verify`.
    /// Does not verify auth proof.
    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        rng: &mut R,
        common_proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        balance_proof: Option<&BalanceChangeSplitProof<F0, G0>>,
        challenge: &F0,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self.verify_sigma_protocols_and_return_tuples(
            common_proof,
            balance_proof,
            challenge,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rng,
            rmc_0,
        )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }
}

fn old_and_new_host_commitments<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    proof: &CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
    re_randomized_leaf: Affine<G0>,
    updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    legs_with_conf: &[LegVerifierConfig<Affine<G0>>],
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
) -> Result<(Affine<G0>, Affine<G0>)> {
    let is_asset_id_revealed = LegVerifierConfig::is_asset_id_revealed_in_any(&legs_with_conf);

    let asset_id_comm = if is_asset_id_revealed {
        let asset_id = legs_with_conf
            .iter()
            .find_map(|l| l.encryption.asset_id())
            .ok_or_else(|| {
                Error::ProofVerificationError("asset_id revealed but not found in legs".to_string())
            })?;
        Some(account_comm_key.asset_id_gen() * F0::from(asset_id))
    } else {
        None
    };

    let mut y_old = re_randomized_leaf.into_group()
        - proof
            .auth_proof
            .partial_re_randomized_account_commitment
            .into_group();
    if let Some(adj) = &asset_id_comm {
        y_old -= adj;
    }
    let y_old = y_old.into_affine();

    let mut y_new = updated_account_commitment.0.into_group()
        - proof
            .auth_proof
            .partial_updated_account_commitment
            .into_group();
    if let Some(adj) = &asset_id_comm {
        y_new -= adj;
    }
    let counter_gen = account_comm_key.counter_gen().into_group();
    for leg_conf in legs_with_conf {
        if let Some(has_counter_decreased) = leg_conf.has_counter_decreased {
            if has_counter_decreased {
                y_new += counter_gen;
            } else {
                y_new -= counter_gen;
            }
        }
    }
    let y_new = y_new.into_affine();
    Ok((y_old, y_new))
}
