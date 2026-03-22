use crate::Balance;
use crate::account::state::{BALANCE_GEN_INDEX, NUM_GENERATORS, SK_ENC_INV_GEN_INDEX};
use crate::account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment};
use crate::leg::{LegEncryption, PartyEphemeralPublicKey};
use crate::util::generate_schnorr_responses_for_balance_change;
use crate::util::{
    BPProof, add_verification_tuples_to_rmc, enforce_balance_change_prover,
    enforce_balance_change_verifier,
    enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change,
    generate_sigma_responses_for_common_state_change, generate_sigma_t_values_for_balance_change,
    generate_sigma_t_values_for_common_state_change, get_verification_tuples_with_rng,
    prove_with_rng, take_challenge_contrib_of_sigma_t_values_for_balance_change,
    verify_given_verification_tuples, verify_sigma_for_balance_change,
    verify_sigma_for_common_state_change,
};
use crate::{
    Error, LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_EVEN_LABEL,
    TXN_ODD_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript, error::Result,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::io::{Read, Write};
use ark_std::{format, string::ToString, vec::Vec};
use bulletproofs::BulletproofGens;
use bulletproofs::PedersenGens;
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use dock_crypto_utils::transcript::Transcript;
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    PartialPokDiscreteLog, PartialPokPedersenCommitment, PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrCommitment, SchnorrResponse};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Proof for variables that change during each account state transition
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonStateChangeProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// When this is None, external [`R1CSProof`] will be used and [`CommonStateChangeProof`] only
    /// contains proof for the sigma protocols and enforces the Bulletproof constraints.
    pub r1cs_proof: Option<BPProof<G0, G1>>,
    /// When using batched proving (multi-asset state transitions),
    /// this will be None as the path is computed externally.
    /// For non-batched proving, this contains the full re-randomized path.
    pub re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: PartialSchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,
    pub resp_leg_link: Vec<LegAccountLink<G0>>,
    /// Commitment to initial rho, old and current rho, old and current randomness
    pub comm_bp_randomness_relations: Affine<G0>,
    /// Commitment to randomness for proving knowledge of above 5 values (step 1 of Schnorr)
    pub t_bp_randomness_relations: Affine<G0>,
    /// Response for proving knowledge of above 5 values (step 3 of Schnorr)
    pub resp_bp_randomness_relations: PartialSchnorrResponse<Affine<G0>>,
}

#[derive(Zeroize, ZeroizeOnDrop)]
pub struct CommonStateChangeProver<
    'a,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    #[zeroize(skip)]
    pub even_prover: Option<Prover<'a, MerlinTranscript, Affine<G0>>>,
    #[zeroize(skip)]
    pub odd_prover: Option<Prover<'a, MerlinTranscript, Affine<G1>>>,
    #[zeroize(skip)]
    pub re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    pub leaf_rerandomization: F0,
    #[zeroize(skip)]
    pub nullifier: Affine<G0>,
    pub t_r_leaf: SchnorrCommitment<Affine<G0>>,
    pub t_acc_new: SchnorrCommitment<Affine<G0>>,
    pub t_null: PokDiscreteLogProtocol<Affine<G0>>,
    #[zeroize(skip)]
    pub t_leg_link: Vec<LegAccountLinkProtocol<G0>>,
    #[zeroize(skip)]
    pub comm_bp_randomness_relations: Affine<G0>,
    pub t_bp_randomness_relations: SchnorrCommitment<Affine<G0>>,
    pub comm_bp_blinding: F0,
    pub sk_enc_inv_blinding: F0,
    pub old_balance_blinding: F0,
    pub new_balance_blinding: F0,
    pub is_asset_id_revealed: bool,
}

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
    pub has_balance_changed: bool,
    pub prover_is_sender: Vec<bool>,
    /// Balance can increase, decrease or not change at all
    pub has_balance_decreased: Vec<Option<bool>>,
    /// Counter can increase, decrease or not change at all
    pub has_counter_decreased: Vec<Option<bool>>,
    pub re_randomized_leaf: Affine<G0>,
}

impl<
    'a,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonStateChangeProver<'a, L, F0, F1, G0, G1>
{
    pub fn init<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        account_tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.sl_params.pc_gens(),
            transcript_even,
        );
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.sl_params.pc_gens(),
            transcript_odd,
        );

        let mut prover = Self::init_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            legs_with_conf,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            account_tree_root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )?;
        prover.even_prover = Some(even_prover);
        prover.odd_prover = Some(odd_prover);
        Ok(prover)
    }

    pub fn gen_proof<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        mut self,
        rng: &mut R,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        challenge: &F0,
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters0>,
    ) -> Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
        let even_prover = self.even_prover.take().ok_or_else(|| {
            Error::ProofGenerationError(
                "even_prover is missing or already consumed; use init() or avoid reusing the prover"
                    .to_string(),
            )
        })?;
        let odd_prover = self.odd_prover.take().ok_or_else(|| {
            Error::ProofGenerationError(
                "odd_prover is missing or already consumed; use init() or avoid reusing the prover"
                    .to_string(),
            )
        })?;

        let mut proof = self.generate_sigma_responses(account, updated_account, challenge)?;

        let bp_gens = account_tree_params.bp_gens();
        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, bp_gens.0, bp_gens.1, rng)?;

        proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });
        Ok(proof)
    }

    pub fn init_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        account_tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<Self> {
        let (re_randomized_path, leaf_rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<_, Parameters0, Parameters1>(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
            )?;

        add_to_transcript!(
            even_prover.transcript(),
            ROOT_LABEL,
            account_tree_root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
        );

        Self::init_with_given_prover_inner(
            rng,
            legs_with_conf,
            account,
            updated_account,
            updated_account_commitment,
            leaf_rerandomization,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            even_prover,
            Some(re_randomized_path),
        )
    }

    /// Creates a new prover when the leaf has already been re-randomized externally.
    /// This is useful for batched proving when proving multiple paths at once.
    /// `rerandomized_leaf_and_blinding` - Tuple of (rerandomized_leaf, re_randomization_of_leaf)
    pub fn init_with_given_prover_with_rerandomized_leaf<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_rerandomization: F0,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
    ) -> Result<Self> {
        // Note: No re_randomized_path to add to transcript since it was computed externally
        // The caller is responsible for adding it to the transcript
        Self::init_with_given_prover_inner(
            rng,
            legs_with_conf,
            account,
            updated_account,
            updated_account_commitment,
            leaf_rerandomization,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            even_prover,
            None, // No path since it was computed externally
        )
    }

    fn init_with_given_prover_inner<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_rerandomization: F0,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    ) -> Result<Self> {
        let enc_key_gen = account_comm_key.sk_enc_gen();
        // has_balance_changed denotes whether the balance changed for any leg. This flag is known to verifier as well
        let has_balance_changed = legs_with_conf.iter().any(|l| l.has_balance_changed);
        ensure_same_accounts(account, updated_account, has_balance_changed)?;

        add_to_transcript!(
            even_prover.transcript(),
            NONCE_LABEL,
            nonce,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        // If asset-id is revealed in any of the leg encryptions, then its assumed that its revealed and the proof
        // is done accordingly
        let mut is_asset_id_revealed = false;
        let mut leg_enc = Vec::with_capacity(legs_with_conf.len());
        let mut is_sender: Vec<bool> = Vec::with_capacity(legs_with_conf.len());

        // For legs that have asset-id ciphertext, prove that asset-id ciphertext is correctly formed when is_asset_id_revealed = true

        for leg_conf in legs_with_conf {
            if let Some(a) = leg_conf.encryption.asset_id() {
                if a != account.asset_id {
                    return Err(Error::ProofGenerationError(format!(
                        "Asset-id mismatch between leg config and account state: leg config = {a}, account = {}",
                        account.asset_id
                    )));
                }
                is_asset_id_revealed = true;
            }
            leg_enc.push(leg_conf.encryption);
            is_sender.push(leg_conf.party_eph_pk.is_sender());
        }

        for l in &leg_enc {
            add_to_transcript!(even_prover.transcript(), LEG_ENC_LABEL, l);
        }

        let mut id_blinding = F0::rand(rng);
        let mut sk_blinding = F0::rand(rng);
        let sk_enc_inv_blinding = F0::rand(rng);
        let mut old_counter_blinding = F0::rand(rng);
        let mut asset_id_blinding = (!is_asset_id_revealed).then(|| F0::rand(rng));
        let mut initial_rho_blinding = F0::rand(rng);
        let mut old_rho_blinding = F0::rand(rng);
        let mut new_rho_blinding = F0::rand(rng);
        let mut old_randomness_blinding = F0::rand(rng);
        let mut new_randomness_blinding = F0::rand(rng);
        let mut initial_randomness_blinding = F0::rand(rng);

        let (old_balance_blinding, new_balance_blinding) = if has_balance_changed {
            (F0::rand(rng), F0::rand(rng))
        } else {
            let b = F0::rand(rng);
            (b, b)
        };

        let (
            nullifier,
            comm_bp_randomness_relations,
            comm_bp_blinding,
            t_r_leaf,
            t_acc_new,
            t_null,
            t_leg_link,
            t_bp_randomness_relations,
        ) = generate_sigma_t_values_for_common_state_change(
            rng,
            account.asset_id,
            leg_enc,
            account,
            updated_account,
            is_sender,
            id_blinding,
            sk_blinding,
            old_balance_blinding,
            new_balance_blinding,
            old_counter_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
            initial_randomness_blinding,
            asset_id_blinding,
            sk_enc_inv_blinding,
            even_prover,
            &account_comm_key,
            account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            enc_key_gen,
            enc_gen,
        )?;

        Zeroize::zeroize(&mut id_blinding);
        Zeroize::zeroize(&mut sk_blinding);
        Zeroize::zeroize(&mut old_counter_blinding);
        Zeroize::zeroize(&mut asset_id_blinding);
        Zeroize::zeroize(&mut initial_rho_blinding);
        Zeroize::zeroize(&mut old_rho_blinding);
        Zeroize::zeroize(&mut new_rho_blinding);
        Zeroize::zeroize(&mut old_randomness_blinding);
        Zeroize::zeroize(&mut new_randomness_blinding);
        Zeroize::zeroize(&mut initial_randomness_blinding);

        Ok(Self {
            even_prover: None,
            odd_prover: None,
            re_randomized_path,
            leaf_rerandomization,
            nullifier,
            t_r_leaf,
            t_acc_new,
            t_null,
            t_leg_link,
            comm_bp_randomness_relations,
            t_bp_randomness_relations,
            comm_bp_blinding,
            sk_enc_inv_blinding,
            old_balance_blinding,
            new_balance_blinding,
            is_asset_id_revealed,
        })
    }

    pub fn generate_sigma_responses(
        mut self,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        challenge: &F0,
    ) -> Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
        let (resp_leaf, resp_acc_new, resp_null, resp_leg_link, resp_bp_randomness_relations) =
            generate_sigma_responses_for_common_state_change(
                account,
                updated_account,
                self.leaf_rerandomization,
                self.comm_bp_blinding,
                &self.t_r_leaf,
                &self.t_acc_new,
                self.t_null.clone(),
                self.t_leg_link.clone(),
                &self.t_bp_randomness_relations,
                self.is_asset_id_revealed,
                challenge,
            )?;

        Zeroize::zeroize(&mut self.leaf_rerandomization);
        Zeroize::zeroize(&mut self.comm_bp_blinding);

        Ok(CommonStateChangeProof {
            r1cs_proof: None,
            re_randomized_path: self.re_randomized_path.clone(),
            t_r_leaf: self.t_r_leaf.t,
            t_acc_new: self.t_acc_new.t,
            resp_leaf,
            resp_acc_new,
            resp_null,
            resp_leg_link,
            comm_bp_randomness_relations: self.comm_bp_randomness_relations,
            t_bp_randomness_relations: self.t_bp_randomness_relations.t,
            resp_bp_randomness_relations,
        })
    }
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
        legs_with_conf: Vec<LegVerifierConfig<G0>>,
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
        ct_amount: &[(Affine<G0>, Affine<G0>)],
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
            ct_amount,
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
        leg_enc: Vec<LegEncryption<Affine<G0>>>,
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
            leg_enc,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rng,
            rmc_0,
        )?;

        match rmc {
            Some((rmc_0, rmc_1)) => add_verification_tuples_to_rmc(
                even_tuple,
                odd_tuple,
                account_tree_params,
                rmc_0,
                rmc_1,
            ),
            None => verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params),
        }
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
        leg_enc: Vec<LegEncryption<Affine<G0>>>,
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
            leg_enc,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rmc,
        )?;

        let r1cs_proof = common_state_change_proof
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
        legs_with_conf: Vec<LegVerifierConfig<G0>>,
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
        let re_randomized_path = proof.re_randomized_path.as_ref().ok_or_else(|| {
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
        legs_with_conf: Vec<LegVerifierConfig<G0>>,
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
        for leg_conf in &legs_with_conf {
            if asset_id.is_none() {
                asset_id = leg_conf.encryption.asset_id();
            } else if leg_conf.encryption.is_asset_id_revealed()
                && (asset_id != leg_conf.encryption.asset_id())
            {
                return Err(Error::ProofVerificationError(
                    "All legs must have the same asset id".to_string(),
                ));
            }
        }

        // If asset-id is revealed, there would be one less response
        let expected_num_resps = NUM_GENERATORS + { asset_id.is_none() as usize };
        if proof.resp_leaf.len() != expected_num_resps {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                expected_num_resps,
                proof.resp_leaf.len(),
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

        // If asset-id is revealed, there a different relation is used to prove the link between leg and account which requires
        // proving knowledge of sk_enc in addition to sk_enc^{-1} and the inverse relation is enforced in BP.
        let expected_num_resps = 1 + { asset_id.is_some() as usize };
        if proof.resp_bp_randomness_relations.responses.len() != expected_num_resps {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                expected_num_resps,
                proof.resp_bp_randomness_relations.responses.len(),
            ));
        }

        add_to_transcript!(
            even_verifier.transcript(),
            NONCE_LABEL,
            nonce,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let mut leg_enc = Vec::with_capacity(legs_with_conf.len());
        let mut prover_is_sender = Vec::with_capacity(legs_with_conf.len());
        let mut has_counter_decreased = Vec::with_capacity(legs_with_conf.len());
        let mut has_balance_decreased = Vec::with_capacity(legs_with_conf.len());

        for leg_conf in legs_with_conf {
            leg_enc.push(leg_conf.encryption);
            prover_is_sender.push(leg_conf.party_eph_pk.is_sender());
            has_balance_decreased.push(leg_conf.has_balance_decreased);
            has_counter_decreased.push(leg_conf.has_counter_decreased);
        }

        for leg_enc in &leg_enc {
            add_to_transcript!(even_verifier.transcript(), LEG_ENC_LABEL, leg_enc,);
        }

        enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change(
            leg_enc,
            &prover_is_sender,
            asset_id,
            &nullifier,
            proof.comm_bp_randomness_relations,
            &proof.t_r_leaf,
            &proof.t_acc_new,
            &proof.t_bp_randomness_relations,
            &proof.resp_null,
            &proof.resp_leg_link,
            even_verifier,
            account_comm_key,
            enc_gen,
        )?;
        // External `Verifier`s will be used to verify this
        Ok(Self {
            even_verifier: None,
            odd_verifier: None,
            has_balance_changed,
            prover_is_sender,
            has_counter_decreased,
            has_balance_decreased,
            re_randomized_leaf,
        })
    }

    pub fn init_balance_change_verification_with_given_verifier(
        &mut self,
        proof: &BalanceChangeProof<F0, G0>,
        ct_amount: &[(Affine<G0>, Affine<G0>)],
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    ) -> Result<()> {
        if self.has_balance_changed {
            let has_balance_decreased = self
                .has_balance_decreased
                .iter()
                .filter(|b| b.is_some())
                .map(|b| b.unwrap())
                .collect::<Vec<_>>();
            enforce_balance_change_verifier(
                proof.comm_bp_bal,
                has_balance_decreased,
                even_verifier,
            )?;
        } else {
            return Err(Error::ProofVerificationError("`has_balance_decreased` wasn't set but still trying to take challenge contribution".into()));
        }

        let mut verifier_transcript = even_verifier.transcript();

        take_challenge_contrib_of_sigma_t_values_for_balance_change(
            ct_amount,
            &proof.t_comm_bp_bal,
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
        leg_enc: Vec<LegEncryption<Affine<G0>>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let pc_gens = account_tree_params.even_parameters.pc_gens();
        let bp_gens = account_tree_params.even_parameters.bp_gens();

        let asset_id = verify_sigma_for_common_state_change(
            &leg_enc,
            self.prover_is_sender.clone(),
            self.has_counter_decreased,
            balance_change_proof.is_some(),
            &nullifier,
            &self.re_randomized_leaf,
            &updated_account_commitment.0,
            &common_state_change_proof.comm_bp_randomness_relations,
            &common_state_change_proof.t_r_leaf,
            &common_state_change_proof.t_acc_new,
            &common_state_change_proof.t_bp_randomness_relations,
            &common_state_change_proof.resp_leaf,
            &common_state_change_proof.resp_acc_new,
            &common_state_change_proof.resp_null,
            &common_state_change_proof.resp_leg_link,
            &common_state_change_proof.resp_bp_randomness_relations,
            &challenge,
            account_comm_key,
            pc_gens,
            bp_gens,
            enc_gen,
            rmc.as_deref_mut(),
        )?;

        if let Some(balance_change_proof) = balance_change_proof {
            // Filter leg_enc and prover_is_sender to only include legs with balance changes
            let (leg_enc, prover_is_sender): (Vec<_>, Vec<_>) = leg_enc
                .into_iter()
                .zip(self.prover_is_sender.into_iter())
                .zip(self.has_balance_decreased.iter())
                .filter(|((_, _), has_bal_dec)| has_bal_dec.is_some())
                .map(|((leg, is_sender), _)| (leg, is_sender))
                .unzip();

            verify_sigma_for_balance_change(
                &leg_enc,
                prover_is_sender,
                &balance_change_proof.resp_leg_amount,
                &balance_change_proof.comm_bp_bal,
                &balance_change_proof.t_comm_bp_bal,
                &balance_change_proof.resp_comm_bp_bal,
                &challenge,
                *common_state_change_proof
                    .resp_leaf
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
                *common_state_change_proof
                    .resp_leaf
                    .0
                    .get(SK_ENC_INV_GEN_INDEX - asset_id.is_some() as usize)
                    .ok_or_else(|| {
                        Error::ProofVerificationError(format!(
                            "Missing resp_leaf response for sk_enc_inv index {}",
                            SK_ENC_INV_GEN_INDEX - asset_id.is_some() as usize
                        ))
                    })?, // adjust response index for sk_enc^{-1} if asset-id is revealed
                pc_gens,
                bp_gens,
                enc_gen,
                rmc.as_deref_mut(),
            )?;
        }
        Ok(())
    }
}

pub fn ensure_same_accounts<G: AffineRepr>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
    has_balance_changed: bool,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if old_state.id != new_state.id {
            return Err(Error::ProofGenerationError(
                "Identity mismatch between old and new account states".to_string(),
            ));
        }
        if old_state.sk != new_state.sk {
            return Err(Error::ProofGenerationError(
                "Secret key mismatch between old and new account states".to_string(),
            ));
        }
        if old_state.sk_enc_inv != new_state.sk_enc_inv {
            return Err(Error::ProofGenerationError(
                "Secret key inverse mismatch between old and new account states".to_string(),
            ));
        }
        if old_state.asset_id != new_state.asset_id {
            return Err(Error::ProofGenerationError(format!(
                "Asset ID mismatch between old and new account states: old = {}, new = {}",
                old_state.asset_id, new_state.asset_id
            )));
        }
        if old_state.rho != new_state.rho {
            return Err(Error::ProofGenerationError(
                "Initial rho mismatch between old and new account states".to_string(),
            ));
        }
        if has_balance_changed {
            if old_state.balance == new_state.balance {
                return Err(Error::ProofGenerationError(
                    "Balance should have changed but it hasn't".to_string(),
                ));
            }
        } else {
            if old_state.balance != new_state.balance {
                return Err(Error::ProofGenerationError(
                    "Balance shouldn't have changed but it has".to_string(),
                ));
            }
        }
        if old_state.current_rho * old_state.rho != new_state.current_rho {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        if old_state.randomness != new_state.randomness {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        if old_state.current_randomness * old_state.randomness != new_state.current_randomness {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        Ok(())
    }
}

/// Configuration for a leg in common state change operations (prover side)
#[derive(Clone)]
pub struct LegProverConfig<G0: SWCurveConfig + Clone + Copy> {
    pub encryption: LegEncryption<Affine<G0>>,
    pub party_eph_pk: PartyEphemeralPublicKey<Affine<G0>>,
    pub has_balance_changed: bool,
}

/// Configuration for a leg in common state change operations (verifier side)
#[derive(Clone)]
pub struct LegVerifierConfig<G0: SWCurveConfig + Clone + Copy> {
    pub encryption: LegEncryption<Affine<G0>>,
    pub party_eph_pk: PartyEphemeralPublicKey<Affine<G0>>,
    pub has_balance_decreased: Option<bool>,
    pub has_counter_decreased: Option<bool>,
}

/// Configuration for balance change in a single leg
pub struct BalanceChangeConfig<G0: SWCurveConfig + Clone + Copy> {
    pub amount: Balance,
    pub ct_amount: Affine<G0>,
    /// Ephemeral public key for amount: eph_pk_s[2] (sender) or eph_pk_r[2] (receiver)
    pub eph_pk_amount: Affine<G0>,
    pub has_balance_decreased: bool,
}

/// Proof for variables that change only when the account state transition involves a change in account balance
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProof<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: Affine<G0>,
    pub resp_comm_bp_bal: PartialSchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving the leg amount relation:
    /// `ct_amount = eph_pk[2] * sk_enc^{-1} * enc_gen * amount`
    /// Both responses (sk_enc_inv and amount) are shared.
    pub resp_leg_amount: Vec<PartialPokPedersenCommitment<Affine<G0>>>,
}

#[derive(Zeroize, ZeroizeOnDrop)]
pub struct BalanceChangeProver<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub amount: Vec<Balance>,
    pub old_balance: Balance,
    pub new_balance: Balance,
    pub comm_bp_bal_blinding: G0::ScalarField,
    #[zeroize(skip)]
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: SchnorrCommitment<Affine<G0>>,
    pub t_leg_amount: Vec<PokPedersenCommitmentProtocol<Affine<G0>>>,
}

impl<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy>
    BalanceChangeProver<F0, G0>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        balance_change_config: Vec<BalanceChangeConfig<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        mut old_balance_blinding: F0,
        mut new_balance_blinding: F0,
        mut sk_enc_inv_blinding: F0,
        mut even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let mut delta = 0i64;
        for config in &balance_change_config {
            if config.has_balance_decreased {
                delta = delta + (config.amount as i64);
            } else {
                delta = delta - (config.amount as i64);
            }
        }
        let (amount, has_balance_decreased) = if delta > 0 {
            (delta as Balance, true)
        } else {
            (-delta as Balance, false)
        };
        ensure_correct_balance_change(account, updated_account, amount, has_balance_decreased)?;

        let mut amounts = Vec::with_capacity(balance_change_config.len());
        let mut ct_amounts = Vec::with_capacity(balance_change_config.len());
        let mut eph_pk_amounts = Vec::with_capacity(balance_change_config.len());
        let mut has_balance_decreased = Vec::with_capacity(balance_change_config.len());
        for config in balance_change_config {
            amounts.push(config.amount);
            ct_amounts.push(config.ct_amount);
            eph_pk_amounts.push(config.eph_pk_amount);
            has_balance_decreased.push(config.has_balance_decreased);
        }

        let (comm_bp_bal_blinding, comm_bp_bal) = enforce_balance_change_prover(
            rng,
            account.balance,
            updated_account.balance,
            amounts.clone(),
            has_balance_decreased,
            &mut even_prover,
            bp_gens,
        )?;

        let mut transcript = even_prover.transcript();

        let amount_blinding = (0..amounts.len())
            .map(|_| F0::rand(rng))
            .collect::<Vec<_>>();
        let (t_comm_bp_bal, t_leg_amount) = generate_sigma_t_values_for_balance_change(
            rng,
            amounts.clone(),
            ct_amounts,
            old_balance_blinding,
            new_balance_blinding,
            amount_blinding,
            account.sk_enc_inv,
            sk_enc_inv_blinding,
            eph_pk_amounts,
            pc_gens,
            bp_gens,
            enc_gen,
            &mut transcript,
        )?;

        Zeroize::zeroize(&mut old_balance_blinding);
        Zeroize::zeroize(&mut new_balance_blinding);
        Zeroize::zeroize(&mut sk_enc_inv_blinding);

        Ok(Self {
            amount: amounts,
            old_balance: account.balance,
            new_balance: updated_account.balance,
            comm_bp_bal_blinding,
            comm_bp_bal,
            t_comm_bp_bal,
            t_leg_amount,
        })
    }

    pub fn gen_proof(self, challenge: &F0) -> Result<BalanceChangeProof<F0, G0>> {
        let t_comm_bp_bal = self.t_comm_bp_bal.t;
        let (resp_comm_bp_bal, resp_leg_amount) = generate_schnorr_responses_for_balance_change(
            self.amount.clone(),
            self.comm_bp_bal_blinding,
            self.t_comm_bp_bal.clone(),
            self.t_leg_amount.clone(),
            challenge,
        )?;
        Ok(BalanceChangeProof {
            comm_bp_bal: self.comm_bp_bal,
            t_comm_bp_bal,
            resp_comm_bp_bal,
            resp_leg_amount,
        })
    }
}

/// For proving the leg-account linking relation:
/// Depending on asset-id is revealed or not, there are 3 possible cases:
/// AssetIdHidden - `ct_asset_id = eph_pk[3] * {sk_enc^{-1}} + enc_gen * at`
/// Both responses (`sk_enc^{-1}` and asset_id) are shared with other sigma protocols.
///
/// AssetIdRevealed - `ct_s = eph_pk[0] * {sk_enc^{-1}} + enc_key_gen * sk_enc` or `ct_r = eph_pk[1] * {sk_enc^{-1}} + enc_key_gen * sk_enc`
/// Both responses (`sk_enc^{-1}` and `sk_enc`) are shared with other sigma protocols.
///
/// AssetIdRevealedElsewhere - `ct_asset_id - enc_gen * at = eph_pk[3] * {sk_enc^{-1}}`, only witness is `sk_enc^{-1}`
/// This is the case where the leg itself doesn't reveal asset-id but some other leg reveals it thus the prover reveals
/// asset-id here as well
#[derive(Clone, Debug)]
pub enum LegAccountLink<G0: SWCurveConfig> {
    AssetIdHidden(PartialPokPedersenCommitment<Affine<G0>>),
    AssetIdRevealed(PartialPokPedersenCommitment<Affine<G0>>),
    AssetIdRevealedElsewhere(PartialPokDiscreteLog<Affine<G0>>),
}

#[derive(Clone, Debug)]
pub enum LegAccountLinkProtocol<G0: SWCurveConfig> {
    AssetIdHidden(PokPedersenCommitmentProtocol<Affine<G0>>),
    AssetIdRevealed(PokPedersenCommitmentProtocol<Affine<G0>>),
    AssetIdRevealedElsewhere(PokDiscreteLogProtocol<Affine<G0>>),
}

impl<G0: SWCurveConfig> LegAccountLinkProtocol<G0> {
    pub fn pc(&self) -> Option<&PokPedersenCommitmentProtocol<Affine<G0>>> {
        match self {
            Self::AssetIdHidden(p) => Some(p),
            Self::AssetIdRevealed(p) => Some(p),
            _ => None,
        }
    }

    pub fn dl(&self) -> Option<&PokDiscreteLogProtocol<Affine<G0>>> {
        match self {
            Self::AssetIdRevealedElsewhere(p) => Some(p),
            _ => None,
        }
    }

    pub fn gen_partial_proof(self) -> LegAccountLink<G0> {
        match self {
            Self::AssetIdHidden(p) => LegAccountLink::AssetIdHidden(p.gen_partial_proof()),
            Self::AssetIdRevealed(p) => LegAccountLink::AssetIdRevealed(p.gen_partial_proof()),
            Self::AssetIdRevealedElsewhere(p) => {
                LegAccountLink::AssetIdRevealedElsewhere(p.gen_partial_proof())
            }
        }
    }
}

impl<G0: SWCurveConfig> LegAccountLink<G0> {
    pub fn pc(&self) -> Option<&PartialPokPedersenCommitment<Affine<G0>>> {
        match self {
            Self::AssetIdHidden(p) => Some(p),
            Self::AssetIdRevealed(p) => Some(p),
            _ => None,
        }
    }

    pub fn dl(&self) -> Option<&PartialPokDiscreteLog<Affine<G0>>> {
        match self {
            Self::AssetIdRevealedElsewhere(p) => Some(p),
            _ => None,
        }
    }
}

pub fn ensure_correct_balance_change<G: AffineRepr>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
    amount: Balance,
    has_balance_decreased: bool,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if has_balance_decreased {
            if new_state.balance != old_state.balance - amount {
                return Err(Error::ProofGenerationError(
                    "Balance decrease incorrect".to_string(),
                ));
            }
        } else {
            if new_state.balance != old_state.balance + amount {
                return Err(Error::ProofGenerationError(
                    "Balance increase incorrect".to_string(),
                ));
            }
        }
        Ok(())
    }
}

mod serialization {
    use super::*;

    impl<G0: SWCurveConfig> CanonicalSerialize for LegAccountLink<G0> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                LegAccountLink::AssetIdHidden(resp) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    resp.serialize_with_mode(&mut writer, compress)
                }
                LegAccountLink::AssetIdRevealed(resp) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    resp.serialize_with_mode(&mut writer, compress)
                }
                LegAccountLink::AssetIdRevealedElsewhere(resp) => {
                    2u8.serialize_with_mode(&mut writer, compress)?;
                    resp.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                LegAccountLink::AssetIdHidden(resp) => resp.serialized_size(compress),
                LegAccountLink::AssetIdRevealed(resp) => resp.serialized_size(compress),
                LegAccountLink::AssetIdRevealedElsewhere(resp) => resp.serialized_size(compress),
            }
        }
    }

    impl<G0: SWCurveConfig> CanonicalDeserialize for LegAccountLink<G0> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            let discriminant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
            match discriminant {
                0 => Ok(LegAccountLink::AssetIdHidden(
                    PartialPokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                1 => Ok(LegAccountLink::AssetIdRevealed(
                    PartialPokPedersenCommitment::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                2 => Ok(LegAccountLink::AssetIdRevealedElsewhere(
                    PartialPokDiscreteLog::deserialize_with_mode(&mut reader, compress, validate)?,
                )),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G0: SWCurveConfig> Valid for LegAccountLink<G0> {
        fn check(&self) -> Result<(), SerializationError> {
            match self {
                LegAccountLink::AssetIdHidden(resp) => resp.check(),
                LegAccountLink::AssetIdRevealed(resp) => resp.check(),
                LegAccountLink::AssetIdRevealedElsewhere(resp) => resp.check(),
            }
        }
    }
}
