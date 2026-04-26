use crate::account::common::balance::{BalanceChangeSplitProof, BalanceSplitProver};
use crate::account::common::verifier::SplitStateChangeVerifier;
use crate::account::common::{
    CommonAffirmationHostProof, CommonAffirmationSplitProof, CommonAffirmationSplitProtocol,
};
use crate::account::state::NUM_GENERATORS;
use crate::account::state_transition::{
    AccountStateTransitionHostProofBuilder, AccountStateTransitionProofVerifier,
};
use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, LegProverConfig,
    LegVerifierConfig,
};
use crate::auth_proofs::account::AuthProofAffirmation;
use crate::error::{Error, Result};
use crate::util::{
    BPProof, get_verification_tuples_with_rng, handle_verification_tuples, prove_with_rng,
};
use crate::{RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{format, string::ToString, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use core::ops::{Deref, DerefMut};
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;

/// Split proof for account state transition (host/auth separation).
/// Contains the common affirmation proof (host + auth parts) and optional balance proof.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountStateTransitionSplitProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
    pub balance_proof: Option<BalanceChangeSplitProof<F0, G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AccountStateTransitionSplitProof<L, F0, F1, G0, G1>
{
    /// Assemble the final split proof from host data, balance proof, and auth proof.
    pub fn assemble(
        host_data: CommonAffirmationHostProof<L, F0, F1, G0, G1>,
        balance_proof: Option<BalanceChangeSplitProof<F0, G0>>,
        auth_proof: AuthProofAffirmation<Affine<G0>>,
    ) -> Self {
        Self {
            common_proof: CommonAffirmationSplitProof::assemble(host_data, auth_proof),
            balance_proof,
        }
    }
}

pub struct AccountStateTransitionSplitProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub inner: CommonAffirmationSplitProtocol<L, F0, F1, G0, G1>,
    pub balance_prover: Option<BalanceSplitProver<F0, G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AccountStateTransitionSplitProtocol<L, F0, F1, G0, G1>
{
    /// Returns the rerandomized leaf point (needed by the auth proof).
    pub fn rerandomized_leaf(&self) -> Affine<G0> {
        self.inner.rerandomized_leaf()
    }

    /// Returns auth's share of the leaf rerandomization scalar.
    pub fn auth_rerandomization(&self) -> F0 {
        self.inner.auth_rerandomization
    }

    /// Returns the commitment randomness for auth's new commitment part.
    pub fn auth_rand_new_comm(&self) -> F0 {
        self.inner.auth_rand_new_comm()
    }

    /// Returns the old balance blinding from the host commitment protocol.
    pub fn old_balance_blinding(&self) -> F0 {
        self.inner.old_balance_blinding()
    }

    /// Returns the new balance blinding from the host commitment protocol.
    pub fn new_balance_blinding(&self) -> F0 {
        self.inner.new_balance_blinding()
    }

    /// Generate the host's proof with owned provers. Finalizes the Bulletproof.
    /// Challenge must be derived externally by the caller.
    pub fn gen_proof<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        challenge: &F0,
        even_prover: Prover<'_, MerlinTranscript, Affine<G0>>,
        odd_prover: Prover<'_, MerlinTranscript, Affine<G1>>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        rng: &mut R,
    ) -> Result<(
        CommonAffirmationHostProof<L, F0, F1, G0, G1>,
        Option<BalanceChangeSplitProof<F0, G0>>,
    )> {
        let host_proof = self.inner.gen_proof::<_, Parameters0, Parameters1>(
            challenge,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )?;
        let balance_proof = Self::gen_balance_proof(self.balance_prover, challenge)?;
        Ok((host_proof, balance_proof))
    }

    /// Generate the host's proof with borrowed prover (for batched multi-asset).
    /// Challenge must be derived externally by the caller.
    pub fn gen_proof_partial(
        self,
        challenge: &F0,
    ) -> Result<(
        CommonAffirmationHostProof<L, F0, F1, G0, G1>,
        Option<BalanceChangeSplitProof<F0, G0>>,
    )> {
        let host_data = self.inner.gen_proof_partial(challenge)?;
        let balance_proof = Self::gen_balance_proof(self.balance_prover, challenge)?;
        Ok((host_data, balance_proof))
    }

    fn gen_balance_proof(
        balance_prover: Option<BalanceSplitProver<F0, G0>>,
        challenge: &F0,
    ) -> Result<Option<BalanceChangeSplitProof<F0, G0>>> {
        if let Some(bp) = balance_prover {
            let (partial, resp_ct_amount) = bp.gen_proof(challenge)?;
            Ok(Some(BalanceChangeSplitProof {
                partial,
                resp_ct_amount,
            }))
        } else {
            Ok(None)
        }
    }
}

pub struct AccountStateTransitionSplitProofBuilder<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub(crate) host: AccountStateTransitionHostProofBuilder<L, F0, F1, G0, G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AccountStateTransitionSplitProofBuilder<L, F0, F1, G0, G1>
{
    pub fn new(
        account: AccountState<Affine<G0>>,
        updated_account: AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nonce: &[u8],
    ) -> Self {
        Self {
            host: AccountStateTransitionHostProofBuilder::new(
                account,
                updated_account,
                updated_account_commitment,
                nonce,
            ),
        }
    }

    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        rng: &mut R,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        k_amounts: &[F0],
        k_asset_ids: &[F0],
    ) -> Result<(
        AccountStateTransitionSplitProtocol<L, F0, F1, G0, G1>,
        Prover<'a, MerlinTranscript, Affine<G0>>,
        Prover<'a, MerlinTranscript, Affine<G1>>,
        Affine<G0>,
    )> {
        self.host.pre_finalize_checks()?;

        let num_balance_decreases = self.host.balance_changes.len();
        if k_amounts.len() != num_balance_decreases {
            return Err(Error::ProofGenerationError(format!(
                "k_amounts length {} does not match number of balance-changing legs {}",
                k_amounts.len(),
                num_balance_decreases
            )));
        }

        let num_hidden_asset_ids = LegProverConfig::num_hidden_asset_ids(&self.host.legs);

        if k_asset_ids.len() != num_hidden_asset_ids {
            return Err(Error::ProofGenerationError(format!(
                "k_asset_ids length {} does not match expected {}",
                k_asset_ids.len(),
                num_hidden_asset_ids
            )));
        }

        let balance_changes = self.host.balance_changes;
        let (inner, mut even_prover, odd_prover, nullifier) =
            CommonAffirmationSplitProtocol::init::<_, Parameters0, Parameters1>(
                rng,
                self.host.legs,
                &self.host.account,
                &self.host.updated_account,
                self.host.updated_account_commitment,
                leaf_path,
                root,
                &self.host.nonce,
                account_tree_params,
                account_comm_key,
                enc_gen,
                k_asset_ids,
            )?;

        // Create balance prover after CommonAffirmationSplitProtocol init
        let balance_prover = if !balance_changes.is_empty() {
            Some(BalanceSplitProver::init(
                rng,
                &balance_changes,
                self.host.account.balance,
                self.host.updated_account.balance,
                inner.old_balance_blinding(),
                inner.new_balance_blinding(),
                enc_gen,
                k_amounts,
                &mut even_prover,
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
            )?)
        } else {
            None
        };

        Ok((
            AccountStateTransitionSplitProtocol {
                inner,
                balance_prover,
            },
            even_prover,
            odd_prover,
            nullifier,
        ))
    }

    pub fn finalize_with_given_prover_with_rerandomized_leaf<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        rng: &mut R,
        leaf_rerandomization: F0,
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        k_amounts: &[F0],
        k_asset_ids: &[F0],
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
    ) -> Result<(
        AccountStateTransitionSplitProtocol<L, F0, F1, G0, G1>,
        Affine<G0>,
    )> {
        self.host.pre_finalize_checks()?;

        let num_balance_decreases = self.host.balance_changes.len();
        if k_amounts.len() != num_balance_decreases {
            return Err(Error::ProofGenerationError(format!(
                "k_amounts length {} does not match number of balance-changing legs {}",
                k_amounts.len(),
                num_balance_decreases
            )));
        }

        let num_hidden_asset_ids = LegProverConfig::num_hidden_asset_ids(&self.host.legs);

        if k_asset_ids.len() != num_hidden_asset_ids {
            return Err(Error::ProofGenerationError(format!(
                "k_asset_ids length {} does not match expected {}",
                k_asset_ids.len(),
                num_hidden_asset_ids
            )));
        }

        let balance_changes = self.host.balance_changes;
        let (inner, nullifier) =
            CommonAffirmationSplitProtocol::init_with_given_prover_with_rerandomized_leaf::<
                _,
                Parameters0,
                Parameters1,
            >(
                rng,
                self.host.legs,
                &self.host.account,
                &self.host.updated_account,
                self.host.updated_account_commitment,
                leaf_rerandomization,
                &self.host.nonce,
                account_tree_params,
                account_comm_key,
                enc_gen,
                k_asset_ids,
                even_prover,
            )?;

        // Create balance prover after CommonAffirmationSplitProtocol init
        let balance_prover = if !balance_changes.is_empty() {
            Some(BalanceSplitProver::init(
                rng,
                &balance_changes,
                self.host.account.balance,
                self.host.updated_account.balance,
                inner.old_balance_blinding(),
                inner.new_balance_blinding(),
                enc_gen,
                k_amounts,
                even_prover,
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
            )?)
        } else {
            None
        };

        Ok((
            AccountStateTransitionSplitProtocol {
                inner,
                balance_prover,
            },
            nullifier,
        ))
    }

    /// `init` + challenge derivation + `gen_proof` in one call.
    /// Returns `(host_data, balance_proof, rerandomized_leaf, auth_rerandomization, auth_rand_new_comm, nullifier)`.
    /// The caller still creates `auth_proof` and calls `AccountStateTransitionSplitProof::assemble`.
    pub fn prove<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        rng: &mut R,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        k_amounts: &[F0],
        k_asset_ids: &[F0],
    ) -> Result<(
        CommonAffirmationHostProof<L, F0, F1, G0, G1>,
        Option<BalanceChangeSplitProof<F0, G0>>,
        Affine<G0>, // rerandomized_leaf
        F0,         // auth_rerandomization
        F0,         // auth_rand_new_comm
        Affine<G0>, // nullifier
    )> {
        let (protocol, mut even_prover, odd_prover, nullifier) = self
            .init::<_, Parameters0, Parameters1>(
                rng,
                leaf_path,
                root,
                account_tree_params,
                account_comm_key,
                enc_gen,
                k_amounts,
                k_asset_ids,
            )?;
        let rerandomized_leaf = protocol.rerandomized_leaf();
        let auth_rerandomization = protocol.auth_rerandomization();
        let auth_rand_new_comm = protocol.auth_rand_new_comm();
        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        let (host_data, balance_proof) = protocol.gen_proof::<_, Parameters0, Parameters1>(
            &challenge,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )?;
        Ok((
            host_data,
            balance_proof,
            rerandomized_leaf,
            auth_rerandomization,
            auth_rand_new_comm,
            nullifier,
        ))
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> Deref for AccountStateTransitionSplitProofBuilder<L, F0, F1, G0, G1>
{
    type Target = AccountStateTransitionHostProofBuilder<L, F0, F1, G0, G1>;
    fn deref(&self) -> &Self::Target {
        &self.host
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> DerefMut for AccountStateTransitionSplitProofBuilder<L, F0, F1, G0, G1>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.host
    }
}

/// Split verification methods for AccountStateTransitionProofVerifier.
impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>
{
    fn pre_verify_checks_split(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
    ) -> Result<()> {
        if self.legs.is_empty() {
            return Err(Error::ProofVerificationError(
                "No legs added to the verifier".to_string(),
            ));
        }

        let num_balance_decreases = self
            .legs
            .iter()
            .filter(|l| l.has_balance_decreased.is_some())
            .count();

        let num_hidden_asset_ids = LegVerifierConfig::num_hidden_asset_ids(&self.legs);

        if proof.common_proof.auth_proof.partial_ct_asset_ids.len() != num_hidden_asset_ids {
            return Err(Error::ProofVerificationError(format!(
                "Invalid proof.auth_proof.partial_ct_asset_ids length. Expected {}, got {}",
                num_hidden_asset_ids,
                proof.common_proof.auth_proof.partial_ct_asset_ids.len()
            )));
        }

        if proof.common_proof.resp_ct_asset_id.len() != num_hidden_asset_ids {
            return Err(Error::ProofVerificationError(format!(
                "Invalid proof.resp_ct_asset_id length. Expected {}, got {}",
                num_hidden_asset_ids,
                proof.common_proof.resp_ct_asset_id.len()
            )));
        }

        if proof.common_proof.auth_proof.partial_ct_amounts.len() != num_balance_decreases {
            return Err(Error::ProofVerificationError(format!(
                "Invalid common_proof.auth_proof.partial_ct_amounts length. Expected {}, got {}",
                num_balance_decreases,
                proof.common_proof.auth_proof.partial_ct_amounts.len()
            )));
        }

        if num_balance_decreases > 0 {
            if let Some(balance_proof) = &proof.balance_proof {
                if balance_proof.resp_ct_amount.len() != num_balance_decreases {
                    return Err(Error::ProofVerificationError(format!(
                        "{num_balance_decreases} legs with balance change but balance change proof for {} legs provided",
                        balance_proof.resp_ct_amount.len()
                    )));
                }
            } else {
                return Err(Error::ProofVerificationError(format!(
                    "{num_balance_decreases} legs with balance change but no balance change proof provided"
                )));
            }
        }

        let is_asset_id_revealed = num_hidden_asset_ids != self.legs.len();
        let expected_host_comm_resp_len = if is_asset_id_revealed {
            NUM_GENERATORS - 2
        } else {
            NUM_GENERATORS - 1
        };

        if proof
            .common_proof
            .host_commitment_proof
            .resp_acc_old
            .0
            .len()
            != expected_host_comm_resp_len
        {
            return Err(Error::ProofVerificationError(format!(
                "Invalid host commitment resp_acc_old length. Expected {}, got {}",
                expected_host_comm_resp_len,
                proof
                    .common_proof
                    .host_commitment_proof
                    .resp_acc_old
                    .0
                    .len()
            )));
        }

        let expected_resp_acc_new_len = 3 + if num_balance_decreases > 0 { 1 } else { 0 };
        if proof
            .common_proof
            .host_commitment_proof
            .resp_acc_new
            .responses
            .len()
            != expected_resp_acc_new_len
        {
            return Err(Error::ProofVerificationError(format!(
                "Invalid host commitment resp_acc_new length. Expected {}, got {}",
                expected_resp_acc_new_len,
                proof
                    .common_proof
                    .host_commitment_proof
                    .resp_acc_new
                    .responses
                    .len()
            )));
        }

        Ok(())
    }

    /// Set up BP constraints and challenge contributions for standalone split verification.
    /// Creates own verifiers. Returns a `SplitStateChangeVerifier` whose transcript can
    /// be used to derive the challenge.
    pub fn challenge_contribution_split<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
    ) -> Result<SplitStateChangeVerifier<L, F0, F1, G0, G1>> {
        self.pre_verify_checks_split(proof)?;

        let mut verifier = SplitStateChangeVerifier::init::<Parameters0, Parameters1>(
            &proof.common_proof,
            self.legs.clone(),
            self.updated_account_commitment,
            self.nullifier,
            root,
            &self.nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
        )?;

        if let Some(balance_proof) = &proof.balance_proof {
            let B_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
            verifier.init_balance_change_verification(
                &proof.common_proof,
                balance_proof,
                enc_gen,
                B_blinding,
            )?;
        }

        Ok(verifier)
    }

    /// Set up BP constraints and challenge contributions for batched split verification
    /// with given verifiers.
    pub fn challenge_contribution_split_with_given_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
    ) -> Result<SplitStateChangeVerifier<L, F0, F1, G0, G1>> {
        self.pre_verify_checks_split(proof)?;

        let mut verifier =
            SplitStateChangeVerifier::init_with_given_verifier::<Parameters0, Parameters1>(
                &proof.common_proof,
                self.legs.clone(),
                self.updated_account_commitment,
                self.nullifier,
                root,
                &self.nonce,
                account_tree_params,
                account_comm_key,
                enc_gen,
                even_verifier,
                odd_verifier,
            )?;

        if let Some(balance_proof) = &proof.balance_proof {
            let B_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
            verifier.init_balance_change_verification_with_given_verifier(
                &proof.common_proof,
                balance_proof,
                enc_gen,
                B_blinding,
                even_verifier,
            )?;
        }

        Ok(verifier)
    }

    /// Set up BP constraints and challenge contributions for batched split verification
    /// with a rerandomized leaf (no curve-tree gadget). Only even_verifier needed.
    pub fn challenge_contribution_split_with_given_verifier_with_rerandomized_leaf(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        rerandomized_leaf: Affine<G0>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        B_blinding: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    ) -> Result<SplitStateChangeVerifier<L, F0, F1, G0, G1>> {
        self.pre_verify_checks_split(proof)?;

        let mut verifier =
            SplitStateChangeVerifier::init_with_given_verifier_with_rerandomized_leaf(
                &proof.common_proof,
                self.legs.clone(),
                self.updated_account_commitment,
                self.nullifier,
                rerandomized_leaf,
                &self.nonce,
                account_comm_key,
                enc_gen,
                B_blinding,
                even_verifier,
            )?;

        if let Some(balance_proof) = &proof.balance_proof {
            verifier.init_balance_change_verification_with_given_verifier(
                &proof.common_proof,
                balance_proof,
                enc_gen,
                B_blinding,
                even_verifier,
            )?;
        }

        Ok(verifier)
    }

    /// Verify all sigma protocols and return verification tuples for deferred R1CS verification.
    /// Uses the externally-derived challenge.
    pub fn verify_split_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        verifier: SplitStateChangeVerifier<L, F0, F1, G0, G1>,
        challenge: &F0,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        verifier.verify_sigma_protocols_and_return_tuples(
            &proof.common_proof,
            proof.balance_proof.as_ref(),
            challenge,
            self.updated_account_commitment,
            self.nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rng,
            rmc,
        )
    }

    /// Verify only sigma protocols for batched split verification (shared verifier case).
    pub fn verify_split_sigma_protocols<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        verifier: SplitStateChangeVerifier<L, F0, F1, G0, G1>,
        challenge: &F0,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        verifier.verify_sigma_protocols(
            &proof.common_proof,
            proof.balance_proof.as_ref(),
            challenge,
            self.updated_account_commitment,
            self.nullifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rmc,
        )
    }

    /// `challenge_contribution_split` + challenge derivation + `verify_split_and_return_tuples`.
    /// Returns `(even_tuple, odd_tuple)`.
    /// Note: `auth_proof` verification is the caller's responsibility (independent Ledger step).
    pub fn verify_split_with_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let mut verifier = self.challenge_contribution_split::<Parameters0, Parameters1>(
            proof,
            root,
            account_tree_params,
            account_comm_key,
            enc_gen,
        )?;
        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        self.verify_split_and_return_tuples::<_, Parameters0, Parameters1>(
            proof,
            verifier,
            &challenge,
            account_tree_params,
            account_comm_key,
            enc_gen,
            rng,
            rmc,
        )
    }

    /// verify sigma protocols and R1CS using a given verifier and challenge, then handle tuples.
    pub fn verify_split_with_given_verifier<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        verifier: SplitStateChangeVerifier<L, F0, F1, G0, G1>,
        challenge: &F0,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self
            .verify_split_and_return_tuples::<_, Parameters0, Parameters1>(
                proof,
                verifier,
                challenge,
                account_tree_params,
                account_comm_key,
                enc_gen,
                rng,
                rmc_0,
            )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    /// complete split verification from scratch.
    /// `verify_split_with_tuples` + `handle_verification_tuples`.
    pub fn verify_split<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        proof: &AccountStateTransitionSplitProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self
            .verify_split_with_tuples::<_, Parameters0, Parameters1>(
                proof,
                root,
                account_tree_params,
                account_comm_key,
                enc_gen,
                rng,
                rmc_0,
            )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }
}

/// Host-side protocol state for multi-asset split proof.
/// Created by `init`, consumed by `gen_proof`.
pub struct MultiAssetStateTransitionHostProtocol<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub protocols: Vec<AccountStateTransitionSplitProtocol<L, F0, F1, G0, G1>>,
    pub re_randomized_paths: Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, G0, G1>>,
    pub nullifiers: Vec<Affine<G0>>,
    /// Per-account rerandomized leaves from batched curve-tree rerandomization.
    pub rerandomized_leaves: Vec<Affine<G0>>,
}

impl<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MultiAssetStateTransitionHostProtocol<L, M, F0, F1, G0, G1>
{
    /// Initialize the host protocol for all accounts.
    ///
    /// Performs batched curve-tree rerandomization, then per-account split protocol
    /// initialization (writing to the shared prover transcript).
    ///
    /// Returns `(self, even_prover, odd_prover)`.
    /// Caller should derive the challenge from `even_prover.transcript()` and pass
    /// it to `gen_proof`.
    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        account_builders: Vec<AccountStateTransitionSplitProofBuilder<L, F0, F1, G0, G1>>,
        leaf_paths: Vec<CurveTreeWitnessMultiPath<L, M, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        k_amounts_per_account: &[&[F0]],
        k_asset_ids_per_account: &[&[F0]],
    ) -> Result<(
        Self,
        Prover<'a, MerlinTranscript, Affine<G0>>,
        Prover<'a, MerlinTranscript, Affine<G1>>,
    )> {
        let num_accounts = account_builders.len();
        if num_accounts == 0 {
            return Err(Error::ProofGenerationError(
                "At least one account is required".to_string(),
            ));
        }
        if k_amounts_per_account.len() != num_accounts
            || k_asset_ids_per_account.len() != num_accounts
        {
            return Err(Error::ProofGenerationError(
                "k_amounts/k_asset_ids length must match number of accounts".to_string(),
            ));
        }
        if leaf_paths.iter().fold(0, |acc, p| acc + p.num_indices()) != num_accounts as u32 {
            return Err(Error::ProofGenerationError(
                "Total paths in leaf_paths does not match number of accounts".to_string(),
            ));
        }

        let even_transcript = MerlinTranscript::new(crate::TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(crate::TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens(),
            even_transcript,
        );
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.pc_gens(),
            odd_transcript,
        );

        add_to_transcript!(even_prover.transcript(), ROOT_LABEL, tree_root);

        // Batched curve tree rerandomization
        let mut re_randomized_paths = Vec::with_capacity(leaf_paths.len());
        let mut rerandomized_leaves_and_randomizers = Vec::with_capacity(num_accounts);

        for leaf_path in leaf_paths.iter() {
            let (re_randomized_path, randomizers_of_leaves) = leaf_path
                .batched_select_and_rerandomize_prover_gadget_new::<_, Parameters0, Parameters1>(
                    &mut even_prover,
                    &mut odd_prover,
                    account_tree_params,
                    rng,
                )?;

            add_to_transcript!(
                even_prover.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );

            let rerandomized_leaves = re_randomized_path.path.get_rerandomized_leaves();
            rerandomized_leaves_and_randomizers
                .extend(rerandomized_leaves.into_iter().zip(randomizers_of_leaves));
            re_randomized_paths.push(re_randomized_path);
        }

        debug_assert_eq!(rerandomized_leaves_and_randomizers.len(), num_accounts);

        let all_rerandomized_leaves: Vec<Affine<G0>> = rerandomized_leaves_and_randomizers
            .iter()
            .map(|(leaf, _)| *leaf)
            .collect();

        // Per-account split protocol initialization
        let mut protocols = Vec::with_capacity(num_accounts);
        let mut nullifiers = Vec::with_capacity(num_accounts);

        for (i, builder) in account_builders.into_iter().enumerate() {
            let (_leaf, randomizer) = rerandomized_leaves_and_randomizers[i];
            let (protocol, nullifier) = builder
                .finalize_with_given_prover_with_rerandomized_leaf::<_, Parameters0, Parameters1>(
                    rng,
                    randomizer,
                    account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    k_amounts_per_account[i],
                    k_asset_ids_per_account[i],
                    &mut even_prover,
                )?;

            protocols.push(protocol);
            nullifiers.push(nullifier);
        }

        Ok((
            Self {
                protocols,
                re_randomized_paths,
                nullifiers,
                rerandomized_leaves: all_rerandomized_leaves,
            },
            even_prover,
            odd_prover,
        ))
    }

    /// Generate the host proof for all accounts.
    ///
    /// Calls `gen_proof_partial` per account and finalizes the shared R1CS provers.
    pub fn gen_proof<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        challenge: &F0,
        even_prover: Prover<'_, MerlinTranscript, Affine<G0>>,
        odd_prover: Prover<'_, MerlinTranscript, Affine<G1>>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        rng: &mut R,
    ) -> Result<(
        Vec<(
            CommonAffirmationHostProof<L, F0, F1, G0, G1>,
            Option<BalanceChangeSplitProof<F0, G0>>,
        )>,
        Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, G0, G1>>,
        BPProof<G0, G1>,
    )> {
        let mut account_data = Vec::with_capacity(self.protocols.len());

        for protocol in self.protocols {
            let (host_data, balance_proof) = protocol.gen_proof_partial(challenge)?;
            account_data.push((host_data, balance_proof));
        }

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;

        Ok((
            account_data,
            self.re_randomized_paths,
            BPProof {
                even_proof,
                odd_proof,
            },
        ))
    }
}

/// Combined multi-asset split proof.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MultiAssetStateTransitionSplitProof<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// Per-account split proofs (each without re_randomized_path and r1cs_proof).
    pub account_proofs: Vec<AccountStateTransitionSplitProof<L, F0, F1, G0, G1>>,
    /// Batched re-randomized paths for all accounts.
    pub re_randomized_paths: Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, G0, G1>>,
    /// Shared R1CS proof.
    pub r1cs_proof: Option<BPProof<G0, G1>>,
}

impl<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MultiAssetStateTransitionSplitProof<L, M, F0, F1, G0, G1>
{
    /// Assemble the final proof from host data, auth proofs, paths, and R1CS proof.
    pub fn assemble(
        account_data: Vec<(
            CommonAffirmationHostProof<L, F0, F1, G0, G1>,
            Option<BalanceChangeSplitProof<F0, G0>>,
        )>,
        auth_proofs: Vec<AuthProofAffirmation<Affine<G0>>>,
        re_randomized_paths: Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, G0, G1>>,
        r1cs_proof: BPProof<G0, G1>,
    ) -> Self {
        let account_proofs = account_data
            .into_iter()
            .zip(auth_proofs)
            .map(|((host_data, balance_proof), auth_proof)| {
                AccountStateTransitionSplitProof::assemble(host_data, balance_proof, auth_proof)
            })
            .collect();
        Self {
            account_proofs,
            re_randomized_paths,
            r1cs_proof: Some(r1cs_proof),
        }
    }

    /// Step 1 of verification: set up BP constraints and challenge contributions.
    ///
    /// Returns:
    /// - per-account `SplitStateChangeVerifier`s
    /// - per-account rerandomized leaves (needed by auth proof verification)
    /// - shared even/odd verifiers (caller derives challenge from `even_verifier.transcript()`)
    pub fn challenge_contribution<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        account_verifiers: &[AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>],
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
    ) -> Result<(
        Vec<SplitStateChangeVerifier<L, F0, F1, G0, G1>>,
        Vec<Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
    )> {
        if self.account_proofs.len() != account_verifiers.len() {
            return Err(Error::ProofVerificationError(format!(
                "Number of proofs ({}) does not match number of verifiers ({})",
                self.account_proofs.len(),
                account_verifiers.len()
            )));
        }

        let even_transcript = MerlinTranscript::new(crate::TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(crate::TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(even_transcript);
        let mut odd_verifier = Verifier::new(odd_transcript);

        add_to_transcript!(even_verifier.transcript(), ROOT_LABEL, tree_root);

        // Verify batched curve tree rerandomization and extract leaves
        let mut rerandomized_leaves = Vec::with_capacity(self.account_proofs.len());
        for re_randomized_path in &self.re_randomized_paths {
            re_randomized_path
                .batched_select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
                    tree_root,
                    &mut even_verifier,
                    &mut odd_verifier,
                    account_tree_params,
                )?;

            add_to_transcript!(
                even_verifier.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );

            rerandomized_leaves.extend(re_randomized_path.path.get_rerandomized_leaves());
        }

        if rerandomized_leaves.len() != self.account_proofs.len() {
            return Err(Error::ProofVerificationError(format!(
                "Batched curve-tree produced {} leaves but there are {} account proofs",
                rerandomized_leaves.len(),
                self.account_proofs.len()
            )));
        }

        let B_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

        // Per-account challenge contributions
        let mut split_verifiers = Vec::with_capacity(self.account_proofs.len());
        for (i, acct_verifier) in account_verifiers.iter().enumerate() {
            let split_verifier = acct_verifier
                .challenge_contribution_split_with_given_verifier_with_rerandomized_leaf(
                    &self.account_proofs[i],
                    rerandomized_leaves[i],
                    account_comm_key,
                    enc_gen,
                    B_blinding,
                    &mut even_verifier,
                )?;
            split_verifiers.push(split_verifier);
        }

        Ok((
            split_verifiers,
            rerandomized_leaves,
            even_verifier,
            odd_verifier,
        ))
    }

    /// Step 3 of verification: verify sigma protocols and R1CS proof.
    ///
    /// Call after auth proof verification (step 2).
    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        account_verifiers: Vec<AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>>,
        split_verifiers: Vec<SplitStateChangeVerifier<L, F0, F1, G0, G1>>,
        challenge: &F0,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        if account_verifiers.len() != self.account_proofs.len() {
            return Err(Error::ProofVerificationError(format!(
                "account_verifiers length {} does not match account_proofs length {}",
                account_verifiers.len(),
                self.account_proofs.len()
            )));
        }
        if split_verifiers.len() != self.account_proofs.len() {
            return Err(Error::ProofVerificationError(format!(
                "split_verifiers length {} does not match account_proofs length {}",
                split_verifiers.len(),
                self.account_proofs.len()
            )));
        }

        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self
            .verify_and_return_tuples::<_, Parameters0, Parameters1>(
                account_verifiers,
                split_verifiers,
                challenge,
                account_tree_params,
                account_comm_key,
                enc_gen,
                even_verifier,
                odd_verifier,
                rng,
                rmc_0,
            )?;

        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    /// Verify sigma protocols per account, then return verification tuples for
    /// deferred R1CS check.
    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        account_verifiers: Vec<AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>>,
        split_verifiers: Vec<SplitStateChangeVerifier<L, F0, F1, G0, G1>>,
        challenge: &F0,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
        rng: &mut R,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        if account_verifiers.len() != self.account_proofs.len() {
            return Err(Error::ProofVerificationError(format!(
                "account_verifiers length {} does not match account_proofs length {}",
                account_verifiers.len(),
                self.account_proofs.len()
            )));
        }
        if split_verifiers.len() != self.account_proofs.len() {
            return Err(Error::ProofVerificationError(format!(
                "split_verifiers length {} does not match account_proofs length {}",
                split_verifiers.len(),
                self.account_proofs.len()
            )));
        }

        // Verify sigma protocols per account
        for (i, (acct_verifier, split_verifier)) in account_verifiers
            .into_iter()
            .zip(split_verifiers)
            .enumerate()
        {
            let rmc_i = match rmc.as_mut() {
                Some(rmc_ref) => Some(&mut **rmc_ref),
                None => None,
            };
            acct_verifier.verify_split_sigma_protocols::<Parameters0, Parameters1>(
                &self.account_proofs[i],
                split_verifier,
                challenge,
                account_tree_params,
                account_comm_key,
                enc_gen,
                rmc_i,
            )?;
        }

        // R1CS verification
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TXN_CHALLENGE_LABEL;
    use crate::account::common::leg_link::{LegProverConfig, LegVerifierConfig};
    use crate::account::state_transition::AccountStateTransitionProofVerifier;
    use crate::account::tests::{get_tree_with_commitment, setup_gens_new, setup_leg_with_conf};
    use crate::account::{AccountCommitmentKeyTrait, PartyEphemeralPublicKey};
    use crate::account_registration::tests::new_account;
    use crate::auth_proofs::AUTH_TXN_LABEL;
    use crate::auth_proofs::account::AuthProofAffirmation;
    use crate::leg::tests::setup_keys;
    use crate::leg::{Leg, LegEncConfig};
    use crate::util::verify_given_verification_tuples;
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use ark_std::UniformRand;
    use bulletproofs::r1cs::ConstraintSystem;
    use curve_tree_relations::curve_tree::CurveTree;
    use rand::thread_rng;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasFr = ark_pallas::Fr;

    #[test]
    fn test_split_multi_leg_two_senders_one_receiver() {
        // Split proof version of test_multi_leg_two_senders_one_receiver.
        // Carol receives from Alice and Bob (2 receive legs), then claims both.

        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
        let tree_height = 6;

        // Setup keys for Alice, Bob, Carol, and auditor
        let (
            (_, (_, pk_alice_e)),
            (_, (_, pk_bob_e)),
            ((sk_carol, pk_carol), (sk_carol_e, pk_carol_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_send_amount = 100u64;
        let bob_send_amount = 200u64;

        let conf = LegEncConfig {
            parties_see_each_other: true,
            reveal_asset_id: false,
        };

        // Create legs
        let leg_1 = Leg::new(
            pk_alice_e.0,
            pk_carol_e.0,
            alice_send_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_1, _) = leg_1
            .encrypt(&mut rng, conf.clone(), enc_key_gen, enc_gen)
            .unwrap();

        let leg_2 = Leg::new(
            pk_bob_e.0,
            pk_carol_e.0,
            bob_send_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_2, _) = leg_2
            .encrypt(&mut rng, conf.clone(), enc_key_gen, enc_gen)
            .unwrap();

        // Create Carol's account
        let carol_id = PallasFr::rand(&mut rng);
        let sk_carol_scalar = sk_carol.0;
        let sk_carol_e_scalar = sk_carol_e.0;
        let (mut carol_account, _, _, _) =
            new_account(&mut rng, asset_id, pk_carol, pk_carol_e, carol_id);
        carol_account.balance = 500;

        let carol_account_comm = carol_account.commit(account_comm_key.clone()).unwrap();

        let account_tree = get_tree_with_commitment::<L, _>(
            carol_account_comm.clone(),
            &account_tree_params,
            tree_height,
        );

        let carol_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root = account_tree.root_node();
        let nonce = b"carol_nonce_split";

        // Carol receives from both (two counter increments, one randomness refresh — matching builder behavior)
        let mut carol_receives = carol_account.clone();
        carol_receives.counter += 2;
        carol_receives.refresh_randomness_for_state_change();
        let carol_receives_comm = carol_receives.commit(account_comm_key.clone()).unwrap();

        // Split proof: Carol creates multi-leg receive proof

        // Auth provides random split keys (no balance change for receive, so no k_amounts)
        let k_asset_id_1 = PallasFr::rand(&mut rng);
        let k_asset_id_2 = PallasFr::rand(&mut rng);

        let (leg_enc_core_1, eph_pk_1) = leg_enc_1.core_and_eph_keys_for_receiver();
        let (leg_enc_core_2, eph_pk_2) = leg_enc_2.core_and_eph_keys_for_receiver();

        // Host protocol init via builder
        let mut split_builder = AccountStateTransitionSplitProofBuilder::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::new(
            carol_account.clone(),
            carol_receives.clone(),
            carol_receives_comm,
            nonce,
        );
        split_builder.add_receive_affirmation((leg_enc_core_1.clone(), eph_pk_1.clone()));
        split_builder.add_receive_affirmation((leg_enc_core_2.clone(), eph_pk_2.clone()));

        let start = Instant::now();
        let (
            host_data,
            balance_proof,
            re_randomized_leaf,
            auth_rerandomization,
            auth_rand_new_comm,
            nullifier,
        ) = split_builder
            .prove::<_, PallasParams, VestaParams>(
                &mut rng,
                carol_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                &[], // no k_amounts (no balance change)
                &[k_asset_id_1, k_asset_id_2],
            )
            .unwrap();

        // Create auth proof
        let auth_proof = AuthProofAffirmation::new(
            &mut rng,
            sk_carol_scalar,
            sk_carol_e_scalar,
            auth_rerandomization,
            auth_rand_new_comm,
            vec![], // no k_amounts
            vec![k_asset_id_1, k_asset_id_2],
            vec![
                LegProverConfig {
                    encryption: leg_enc_core_1.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_1.clone()),
                    has_balance_changed: false,
                },
                LegProverConfig {
                    encryption: leg_enc_core_2.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_2.clone()),
                    has_balance_changed: false,
                },
            ],
            &re_randomized_leaf,
            &carol_receives_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
            b_blinding,
            enc_gen,
        )
        .unwrap();

        assert!(balance_proof.is_none()); // no balance change for receive

        let proving_time = start.elapsed();

        // Assemble
        let split_proof =
            AccountStateTransitionSplitProof::assemble(host_data, balance_proof, auth_proof);

        println!(
            "Split proof (2 receive legs): proving time = {:?}, proof size = {} bytes",
            proving_time,
            split_proof.compressed_size()
        );

        let mut carol_verifier =
            AccountStateTransitionProofVerifier::init(carol_receives_comm, nullifier, nonce);
        carol_verifier.add_receive_affirmation((leg_enc_core_1.clone(), eph_pk_1.clone()));
        carol_verifier.add_receive_affirmation((leg_enc_core_2.clone(), eph_pk_2.clone()));

        //  Challenge contribution
        let re_randomized_leaf_v = split_proof
            .common_proof
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf();
        split_proof
            .common_proof
            .auth_proof
            .verify(
                vec![
                    LegVerifierConfig {
                        encryption: leg_enc_core_1,
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_1),
                        has_balance_decreased: None,
                        has_counter_decreased: Some(false),
                    },
                    LegVerifierConfig {
                        encryption: leg_enc_core_2,
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_2),
                        has_balance_decreased: None,
                        has_counter_decreased: Some(false),
                    },
                ],
                &re_randomized_leaf_v,
                &carol_receives_comm.0,
                nullifier,
                nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                None,
            )
            .unwrap();

        // Verify sigma protocols
        let (even_tuple, odd_tuple) = carol_verifier
            .verify_split_with_tuples::<_, PallasParams, VestaParams>(
                &split_proof,
                &account_tree_root,
                &account_tree_params,
                &account_comm_key,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();
    }

    #[test]
    fn test_split_multi_leg_sender_and_receiver() {
        // Split proof version of test_multi_leg_sender_and_receiver.
        // Alice sends to Bob and receives from Carol in one multi-leg proof.

        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;

        // Setup keys for Alice, Bob, Carol, and auditor
        let (
            ((sk_alice, pk_alice), (sk_alice_e, pk_alice_e)),
            ((_, _), (_, pk_bob_e)),
            ((_, _), (_, pk_carol_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_to_bob_amount = 100u64;
        let carol_to_alice_amount = 150u64;

        // Create legs
        let leg_1 = Leg::new(
            pk_alice_e.0,
            pk_bob_e.0,
            alice_to_bob_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_1, _) = leg_1
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let leg_2 = Leg::new(
            pk_carol_e.0,
            pk_alice_e.0,
            carol_to_alice_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_2, _) = leg_2
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        // Create Alice's account
        let alice_id = PallasFr::rand(&mut rng);
        let sk_alice_scalar = sk_alice.0;
        let sk_alice_e_scalar = sk_alice_e.0;
        let (mut alice_account, _, _, _) =
            new_account(&mut rng, asset_id, pk_alice, pk_alice_e, alice_id);
        alice_account.balance = 1000;

        // Alice sends and receives (one balance decrement, two counter changes, one randomness refresh — matching builder behavior)
        let mut alice_updated = alice_account.clone();
        alice_updated.balance -= alice_to_bob_amount;
        alice_updated.counter += 2;
        alice_updated.refresh_randomness_for_state_change();
        let alice_account_comm = alice_account.commit(account_comm_key.clone()).unwrap();
        let alice_updated_comm = alice_updated.commit(account_comm_key.clone()).unwrap();

        let account_tree =
            get_tree_with_commitment::<L, _>(alice_account_comm.clone(), &account_tree_params, 6);
        let account_tree_root = account_tree.root_node();
        let alice_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let nonce = b"alice_nonce_split";

        // Auth provides random split keys
        let k_amount = PallasFr::rand(&mut rng); // for the send leg
        let k_asset_id_1 = PallasFr::rand(&mut rng);
        let k_asset_id_2 = PallasFr::rand(&mut rng);

        let (leg_enc_core_1, eph_pk_s_1) = leg_enc_1.core_and_eph_keys_for_sender();
        let (leg_enc_core_2, eph_pk_r_2) = leg_enc_2.core_and_eph_keys_for_receiver();

        // Host protocol init via builder
        let mut split_builder = AccountStateTransitionSplitProofBuilder::<
            L,
            _,
            _,
            PallasParameters,
            VestaParameters,
        >::new(
            alice_account.clone(),
            alice_updated.clone(),
            alice_updated_comm,
            nonce,
        );
        split_builder.add_send_affirmation(
            alice_to_bob_amount,
            (leg_enc_core_1.clone(), eph_pk_s_1.clone()),
        );
        split_builder.add_receive_affirmation((leg_enc_core_2.clone(), eph_pk_r_2.clone()));

        let start = Instant::now();
        let (
            host_data,
            balance_proof,
            re_randomized_leaf,
            auth_rerandomization,
            auth_rand_new_comm,
            nullifier,
        ) = split_builder
            .prove::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                &[k_amount],
                &[k_asset_id_1, k_asset_id_2],
            )
            .unwrap();

        // Create auth proof
        let auth_proof = AuthProofAffirmation::new(
            &mut rng,
            sk_alice_scalar,
            sk_alice_e_scalar,
            auth_rerandomization,
            auth_rand_new_comm,
            vec![k_amount],
            vec![k_asset_id_1, k_asset_id_2],
            vec![
                LegProverConfig {
                    encryption: leg_enc_core_1.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s_1.clone()),
                    has_balance_changed: true,
                },
                LegProverConfig {
                    encryption: leg_enc_core_2.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r_2.clone()),
                    has_balance_changed: false,
                },
            ],
            &re_randomized_leaf,
            &alice_updated_comm.0,
            nullifier,
            nonce,
            account_comm_key.sk_gen(),
            account_comm_key.sk_enc_gen(),
            b_blinding,
            enc_gen,
        )
        .unwrap();

        assert!(balance_proof.is_some()); // send leg has balance change

        let proving_time = start.elapsed();

        // Assemble
        let split_proof =
            AccountStateTransitionSplitProof::assemble(host_data, balance_proof, auth_proof);

        println!(
            "Split proof (1 send + 1 receive): proving time = {:?}, proof size = {} bytes",
            proving_time,
            split_proof.compressed_size()
        );

        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, nullifier, nonce);
        alice_verifier.add_send_affirmation((leg_enc_core_1.clone(), eph_pk_s_1.clone()));
        alice_verifier.add_receive_affirmation((leg_enc_core_2.clone(), eph_pk_r_2.clone()));

        // Challenge contribution
        let re_randomized_leaf_v = split_proof
            .common_proof
            .partial
            .re_randomized_path
            .as_ref()
            .unwrap()
            .path
            .get_rerandomized_leaf();
        split_proof
            .common_proof
            .auth_proof
            .verify(
                vec![
                    LegVerifierConfig {
                        encryption: leg_enc_core_1.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s_1.clone()),
                        has_balance_decreased: Some(true),
                        has_counter_decreased: Some(false),
                    },
                    LegVerifierConfig {
                        encryption: leg_enc_core_2.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r_2.clone()),
                        has_balance_decreased: None,
                        has_counter_decreased: Some(false),
                    },
                ],
                &re_randomized_leaf_v,
                &alice_updated_comm.0,
                nullifier,
                nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                None,
            )
            .unwrap();

        // Verify sigma protocols
        let (even_tuple, odd_tuple) = alice_verifier
            .verify_split_with_tuples::<_, PallasParams, VestaParams>(
                &split_proof,
                &account_tree_root,
                &account_tree_params,
                &account_comm_key,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        verify_given_verification_tuples(even_tuple, odd_tuple, &account_tree_params).unwrap();

        println!("Split multi-leg sender and receiver: verification passed!");
    }

    #[test]
    fn test_split_multi_asset_two_accounts() {
        // Split proof version of test_multi_asset_state_transition_two_accounts.
        // Alice has two accounts: asset 1 (sends to Bob) and asset 2 (receives from Bob).

        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 14;
        const L: usize = 64;
        const M: usize = 2;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
        let tree_height = 6;

        // Setup keys
        let (((sk_alice, pk_alice), (sk_alice_e, pk_alice_e)), ((_, _), (_, pk_bob_e)), _) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id_1 = 1u32;
        let asset_id_2 = 2u32;
        let alice_send_amount = 100u64;
        let bob_send_amount = 200u64;

        let mut test_with_config = |reveal_asset_id: bool| {
            let conf = LegEncConfig {
                parties_see_each_other: true,
                reveal_asset_id,
            };

            // Leg 1: Alice -> Bob (asset 1)
            let (_, leg_enc_1, _) = setup_leg_with_conf(
                &mut rng,
                conf.clone(),
                pk_auditor_e.0,
                None,
                alice_send_amount,
                asset_id_1,
                pk_alice_e.0,
                pk_bob_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Leg 2: Bob -> Alice (asset 2)
            let (_, leg_enc_2, _) = setup_leg_with_conf(
                &mut rng,
                conf.clone(),
                pk_auditor_e.0,
                None,
                bob_send_amount,
                asset_id_2,
                pk_bob_e.0,
                pk_alice_e.0,
                enc_key_gen,
                enc_gen,
            );

            let sk_alice_scalar = sk_alice.0;
            let sk_alice_e_scalar = sk_alice_e.0;

            // Alice's accounts
            let alice_id_1 = PallasFr::rand(&mut rng);
            let (mut alice_account_1, _, _, _) =
                new_account(&mut rng, asset_id_1, pk_alice, pk_alice_e, alice_id_1);
            alice_account_1.balance = 500;

            let alice_id_2 = PallasFr::rand(&mut rng);
            let (mut alice_account_2, _, _, _) =
                new_account(&mut rng, asset_id_2, pk_alice, pk_alice_e, alice_id_2);
            alice_account_2.balance = 300;

            let alice_account_1_comm = alice_account_1.commit(account_comm_key.clone()).unwrap();
            let alice_account_2_comm = alice_account_2.commit(account_comm_key.clone()).unwrap();

            let account_tree = CurveTree::<L, M, PallasParameters, VestaParameters>::from_leaves(
                &[alice_account_1_comm.0, alice_account_2_comm.0],
                &account_tree_params,
                Some(tree_height),
            );

            let account_tree_root = account_tree.root_node();
            let leaf_path = account_tree.get_paths_to_leaves(&[0, 1]).unwrap();

            let alice_nonce = b"alice_nonce";

            // Updated accounts
            let alice_account_1_updated = alice_account_1
                .get_state_for_send(alice_send_amount)
                .unwrap();
            let alice_account_1_updated_comm = alice_account_1_updated
                .commit(account_comm_key.clone())
                .unwrap();

            let alice_account_2_updated = alice_account_2.get_state_for_receive();
            let alice_account_2_updated_comm = alice_account_2_updated
                .commit(account_comm_key.clone())
                .unwrap();

            // Auth random keys
            let k_amount_1 = PallasFr::rand(&mut rng);
            let k_asset_id_1 = PallasFr::rand(&mut rng);
            let k_asset_id_2 = PallasFr::rand(&mut rng);

            // When asset_id is revealed, no k_asset_ids needed
            let k_asset_ids_1: Vec<PallasFr> = if reveal_asset_id {
                vec![]
            } else {
                vec![k_asset_id_1]
            };
            let k_asset_ids_2: Vec<PallasFr> = if reveal_asset_id {
                vec![]
            } else {
                vec![k_asset_id_2]
            };

            // Split builders
            let mut split_builder_1 = AccountStateTransitionSplitProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new(
                alice_account_1.clone(),
                alice_account_1_updated.clone(),
                alice_account_1_updated_comm,
                alice_nonce,
            );
            split_builder_1.add_send_affirmation(
                alice_send_amount,
                (
                    leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                    leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
            );

            let mut split_builder_2 = AccountStateTransitionSplitProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new(
                alice_account_2.clone(),
                alice_account_2_updated.clone(),
                alice_account_2_updated_comm,
                alice_nonce,
            );
            split_builder_2.add_receive_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            // Host protocol init
            let start = Instant::now();
            let (host_protocol, mut even_prover, odd_prover) =
                MultiAssetStateTransitionHostProtocol::<
                    L,
                    M,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init::<_, PallasParams, VestaParams>(
                    &mut rng,
                    vec![split_builder_1, split_builder_2],
                    vec![leaf_path],
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    &[&[k_amount_1], &[]],
                    &[&k_asset_ids_1[..], &k_asset_ids_2[..]],
                )
                .unwrap();

            let challenge_h = {
                let transcript = even_prover.transcript();
                transcript.challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
            };

            // Save data needed after gen_proof consumes host_protocol
            let nullifier_1 = host_protocol.nullifiers[0];
            let nullifier_2 = host_protocol.nullifiers[1];
            let re_rand_leaf_1 = host_protocol.rerandomized_leaves[0];
            let re_rand_leaf_2 = host_protocol.rerandomized_leaves[1];
            let auth_rerand_1 = host_protocol.protocols[0].auth_rerandomization();
            let auth_rerand_2 = host_protocol.protocols[1].auth_rerandomization();
            let auth_rand_new_comm_1 = host_protocol.protocols[0].auth_rand_new_comm();
            let auth_rand_new_comm_2 = host_protocol.protocols[1].auth_rand_new_comm();

            // Auth proofs (shared transcript across accounts)
            let mut auth_transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

            let auth_proof_1 = AuthProofAffirmation::new_with_given_transcript(
                &mut rng,
                sk_alice_scalar,
                sk_alice_e_scalar,
                auth_rerand_1,
                auth_rand_new_comm_1,
                vec![k_amount_1],
                k_asset_ids_1.clone(),
                vec![LegProverConfig {
                    encryption: leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Sender(
                        leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                    ),
                    has_balance_changed: true,
                }],
                &re_rand_leaf_1,
                &alice_account_1_updated_comm.0,
                nullifier_1,
                alice_nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                &mut auth_transcript,
            )
            .unwrap();

            let auth_proof_2 = AuthProofAffirmation::new_with_given_transcript(
                &mut rng,
                sk_alice_scalar,
                sk_alice_e_scalar,
                auth_rerand_2,
                auth_rand_new_comm_2,
                vec![],
                k_asset_ids_2.clone(),
                vec![LegProverConfig {
                    encryption: leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Receiver(
                        leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                    ),
                    has_balance_changed: false,
                }],
                &re_rand_leaf_2,
                &alice_account_2_updated_comm.0,
                nullifier_2,
                alice_nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                &mut auth_transcript,
            )
            .unwrap();

            // Host gen_proof
            let (account_data, re_rand_paths, r1cs_proof) = host_protocol
                .gen_proof::<_, PallasParams, VestaParams>(
                    &challenge_h,
                    even_prover,
                    odd_prover,
                    &account_tree_params,
                    &mut rng,
                )
                .unwrap();

            let proving_time = start.elapsed();

            let split_proof = MultiAssetStateTransitionSplitProof::assemble(
                account_data,
                vec![auth_proof_1, auth_proof_2],
                re_rand_paths,
                r1cs_proof,
            );

            let proof_size = split_proof.compressed_size();
            println!(
                "reveal_asset_id={reveal_asset_id}: Split multi-asset two accounts: proving time = {:?}, proof size = {} bytes",
                proving_time, proof_size
            );

            //  Challenge contribution
            let start = Instant::now();
            let mut alice_verifier_1a = AccountStateTransitionProofVerifier::init(
                alice_account_1_updated_comm,
                nullifier_1,
                alice_nonce,
            );
            alice_verifier_1a.add_send_affirmation((
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ));

            let mut alice_verifier_2a = AccountStateTransitionProofVerifier::init(
                alice_account_2_updated_comm,
                nullifier_2,
                alice_nonce,
            );
            alice_verifier_2a.add_receive_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            let (split_verifiers, rerandomized_leaves, mut even_verifier, odd_verifier) =
                split_proof
                    .challenge_contribution::<PallasParams, VestaParams>(
                        &[alice_verifier_1a, alice_verifier_2a],
                        &account_tree_root,
                        &account_tree_params,
                        &account_comm_key,
                        enc_gen,
                    )
                    .unwrap();

            //  Derive challenge
            let challenge_v = even_verifier
                .transcript()
                .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

            //  Verify auth proofs (shared transcript)
            let mut auth_verify_transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
            split_proof.account_proofs[0]
                .common_proof
                .auth_proof
                .verify_with_given_transcript(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Sender(
                            leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                        ),
                        has_balance_decreased: Some(true),
                        has_counter_decreased: Some(true),
                    }],
                    &rerandomized_leaves[0],
                    &alice_account_1_updated_comm.0,
                    nullifier_1,
                    alice_nonce,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    &mut auth_verify_transcript,
                    None,
                )
                .unwrap();

            split_proof.account_proofs[1]
                .common_proof
                .auth_proof
                .verify_with_given_transcript(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(
                            leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                        ),
                        has_balance_decreased: None,
                        has_counter_decreased: Some(false),
                    }],
                    &rerandomized_leaves[1],
                    &alice_account_2_updated_comm.0,
                    nullifier_2,
                    alice_nonce,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    &mut auth_verify_transcript,
                    None,
                )
                .unwrap();

            //  Verify sigma protocols + R1CS
            let mut alice_verifier_1b = AccountStateTransitionProofVerifier::init(
                alice_account_1_updated_comm,
                nullifier_1,
                alice_nonce,
            );
            alice_verifier_1b.add_send_affirmation((
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ));

            let mut alice_verifier_2b = AccountStateTransitionProofVerifier::init(
                alice_account_2_updated_comm,
                nullifier_2,
                alice_nonce,
            );
            alice_verifier_2b.add_receive_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            split_proof
                .verify::<_, PallasParams, VestaParams>(
                    vec![alice_verifier_1b, alice_verifier_2b],
                    split_verifiers,
                    &challenge_v,
                    &account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    even_verifier,
                    odd_verifier,
                    &mut rng,
                    None,
                )
                .unwrap();

            let verification_time = start.elapsed();
            println!(
                "reveal_asset_id={reveal_asset_id}: Split multi-asset two accounts: verification time = {:?}",
                verification_time
            );
        };

        test_with_config(false);
        test_with_config(true);
    }

    #[test]
    fn test_split_multi_asset_state_transition_two_accounts() {
        // Split proof version of test_multi_asset_state_transition_two_accounts.
        // Alice and Bob both have 2 accounts, 1 per asset.
        // Leg 1: Alice sends Bob asset 1. Leg 2: Bob sends Alice asset 2.
        // Both Alice and Bob each create a split multi-asset proof.

        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 14;
        const L: usize = 64;
        const M: usize = 2;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let b_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
        let tree_height = 6;

        // Setup keys for Alice, Bob, and auditor
        let (
            ((sk_alice, pk_alice), (sk_alice_e, pk_alice_e)),
            ((sk_bob, pk_bob), (sk_bob_e, pk_bob_e)),
            (_, (_, pk_auditor_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id_1 = 1u32;
        let asset_id_2 = 2u32;
        let alice_send_amount = 100u64;
        let bob_send_amount = 200u64;

        let mut test_with_config = |reveal_asset_id: bool| {
            let conf = LegEncConfig {
                parties_see_each_other: true,
                reveal_asset_id,
            };

            // Leg 1: Alice -> Bob (asset 1)
            let (_, leg_enc_1, _) = setup_leg_with_conf(
                &mut rng,
                conf.clone(),
                pk_auditor_e.0,
                None,
                alice_send_amount,
                asset_id_1,
                pk_alice_e.0,
                pk_bob_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Leg 2: Bob -> Alice (asset 2)
            let (_, leg_enc_2, _) = setup_leg_with_conf(
                &mut rng,
                conf.clone(),
                pk_auditor_e.0,
                None,
                bob_send_amount,
                asset_id_2,
                pk_bob_e.0,
                pk_alice_e.0,
                enc_key_gen,
                enc_gen,
            );

            let sk_alice_scalar = sk_alice.0;
            let sk_alice_e_scalar = sk_alice_e.0;
            let sk_bob_scalar = sk_bob.0;
            let sk_bob_e_scalar = sk_bob_e.0;

            // Alice's accounts
            let alice_id_1 = PallasFr::rand(&mut rng);
            let (mut alice_account_1, _, _, _) =
                new_account(&mut rng, asset_id_1, pk_alice, pk_alice_e, alice_id_1);
            alice_account_1.balance = 500;

            let alice_id_2 = PallasFr::rand(&mut rng);
            let (mut alice_account_2, _, _, _) =
                new_account(&mut rng, asset_id_2, pk_alice, pk_alice_e, alice_id_2);
            alice_account_2.balance = 300;

            // Bob's accounts
            let bob_id_1 = PallasFr::rand(&mut rng);
            let (mut bob_account_1, _, _, _) =
                new_account(&mut rng, asset_id_1, pk_bob, pk_bob_e, bob_id_1);
            bob_account_1.balance = 400;

            let bob_id_2 = PallasFr::rand(&mut rng);
            let (mut bob_account_2, _, _, _) =
                new_account(&mut rng, asset_id_2, pk_bob, pk_bob_e, bob_id_2);
            bob_account_2.balance = 800;

            // Commitments
            let alice_account_1_comm = alice_account_1.commit(account_comm_key.clone()).unwrap();
            let alice_account_2_comm = alice_account_2.commit(account_comm_key.clone()).unwrap();
            let bob_account_1_comm = bob_account_1.commit(account_comm_key.clone()).unwrap();
            let bob_account_2_comm = bob_account_2.commit(account_comm_key.clone()).unwrap();

            // Shared tree with all 4 accounts
            let account_tree = CurveTree::<L, M, PallasParameters, VestaParameters>::from_leaves(
                &[
                    alice_account_1_comm.0,
                    alice_account_2_comm.0,
                    bob_account_1_comm.0,
                    bob_account_2_comm.0,
                ],
                &account_tree_params,
                Some(tree_height),
            );
            let account_tree_root = account_tree.root_node();

            // Paths: Alice has leaves [0,1], Bob has leaves [2,3]
            let alice_leaf_path = account_tree.get_paths_to_leaves(&[0, 1]).unwrap();
            let bob_leaf_path = account_tree.get_paths_to_leaves(&[2, 3]).unwrap();

            let alice_nonce = b"alice_nonce";
            let bob_nonce = b"bob_nonce";

            // Updated states
            let alice_account_1_updated = alice_account_1
                .get_state_for_send(alice_send_amount)
                .unwrap();
            let alice_account_1_updated_comm = alice_account_1_updated
                .commit(account_comm_key.clone())
                .unwrap();

            let alice_account_2_updated = alice_account_2.get_state_for_receive();
            let alice_account_2_updated_comm = alice_account_2_updated
                .commit(account_comm_key.clone())
                .unwrap();

            let bob_account_1_updated = bob_account_1.get_state_for_receive();
            let bob_account_1_updated_comm = bob_account_1_updated
                .commit(account_comm_key.clone())
                .unwrap();

            let bob_account_2_updated = bob_account_2.get_state_for_send(bob_send_amount).unwrap();
            let bob_account_2_updated_comm = bob_account_2_updated
                .commit(account_comm_key.clone())
                .unwrap();

            // Auth random keys
            let k_amount_alice = PallasFr::rand(&mut rng);
            let k_amount_bob = PallasFr::rand(&mut rng);
            let k_asset_id_alice_1 = PallasFr::rand(&mut rng);
            let k_asset_id_alice_2 = PallasFr::rand(&mut rng);
            let k_asset_id_bob_1 = PallasFr::rand(&mut rng);
            let k_asset_id_bob_2 = PallasFr::rand(&mut rng);

            let k_asset_ids_alice_1: Vec<PallasFr> = if reveal_asset_id {
                vec![]
            } else {
                vec![k_asset_id_alice_1]
            };
            let k_asset_ids_alice_2: Vec<PallasFr> = if reveal_asset_id {
                vec![]
            } else {
                vec![k_asset_id_alice_2]
            };
            let k_asset_ids_bob_1: Vec<PallasFr> = if reveal_asset_id {
                vec![]
            } else {
                vec![k_asset_id_bob_1]
            };
            let k_asset_ids_bob_2: Vec<PallasFr> = if reveal_asset_id {
                vec![]
            } else {
                vec![k_asset_id_bob_2]
            };

            // ── Alice's split multi-asset proof ──────────────────────────────

            let mut alice_split_builder_1 = AccountStateTransitionSplitProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new(
                alice_account_1.clone(),
                alice_account_1_updated.clone(),
                alice_account_1_updated_comm,
                alice_nonce,
            );
            alice_split_builder_1.add_send_affirmation(
                alice_send_amount,
                (
                    leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                    leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
            );

            let mut alice_split_builder_2 = AccountStateTransitionSplitProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new(
                alice_account_2.clone(),
                alice_account_2_updated.clone(),
                alice_account_2_updated_comm,
                alice_nonce,
            );
            alice_split_builder_2.add_receive_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            let start = Instant::now();
            let (alice_host_protocol, mut alice_even_prover, alice_odd_prover) =
                MultiAssetStateTransitionHostProtocol::<
                    L,
                    M,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init::<_, PallasParams, VestaParams>(
                    &mut rng,
                    vec![alice_split_builder_1, alice_split_builder_2],
                    vec![alice_leaf_path],
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    &[&[k_amount_alice], &[]],
                    &[&k_asset_ids_alice_1[..], &k_asset_ids_alice_2[..]],
                )
                .unwrap();

            let alice_challenge = {
                let transcript = alice_even_prover.transcript();
                transcript.challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
            };

            let alice_nullifier_1 = alice_host_protocol.nullifiers[0];
            let alice_nullifier_2 = alice_host_protocol.nullifiers[1];
            let alice_re_rand_leaf_1 = alice_host_protocol.rerandomized_leaves[0];
            let alice_re_rand_leaf_2 = alice_host_protocol.rerandomized_leaves[1];
            let alice_auth_rerand_1 = alice_host_protocol.protocols[0].auth_rerandomization();
            let alice_auth_rerand_2 = alice_host_protocol.protocols[1].auth_rerandomization();
            let alice_auth_rand_new_comm_1 = alice_host_protocol.protocols[0].auth_rand_new_comm();
            let alice_auth_rand_new_comm_2 = alice_host_protocol.protocols[1].auth_rand_new_comm();

            let mut alice_auth_transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

            let alice_auth_proof_1 = AuthProofAffirmation::new_with_given_transcript(
                &mut rng,
                sk_alice_scalar,
                sk_alice_e_scalar,
                alice_auth_rerand_1,
                alice_auth_rand_new_comm_1,
                vec![k_amount_alice],
                k_asset_ids_alice_1.clone(),
                vec![LegProverConfig {
                    encryption: leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Sender(
                        leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                    ),
                    has_balance_changed: true,
                }],
                &alice_re_rand_leaf_1,
                &alice_account_1_updated_comm.0,
                alice_nullifier_1,
                alice_nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                &mut alice_auth_transcript,
            )
            .unwrap();

            let alice_auth_proof_2 = AuthProofAffirmation::new_with_given_transcript(
                &mut rng,
                sk_alice_scalar,
                sk_alice_e_scalar,
                alice_auth_rerand_2,
                alice_auth_rand_new_comm_2,
                vec![],
                k_asset_ids_alice_2.clone(),
                vec![LegProverConfig {
                    encryption: leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Receiver(
                        leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                    ),
                    has_balance_changed: false,
                }],
                &alice_re_rand_leaf_2,
                &alice_account_2_updated_comm.0,
                alice_nullifier_2,
                alice_nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                &mut alice_auth_transcript,
            )
            .unwrap();

            let (alice_account_data, alice_re_rand_paths, alice_r1cs_proof) = alice_host_protocol
                .gen_proof::<_, PallasParams, VestaParams>(
                    &alice_challenge,
                    alice_even_prover,
                    alice_odd_prover,
                    &account_tree_params,
                    &mut rng,
                )
                .unwrap();
            let alice_proving_time = start.elapsed();

            let alice_split_proof = MultiAssetStateTransitionSplitProof::assemble(
                alice_account_data,
                vec![alice_auth_proof_1, alice_auth_proof_2],
                alice_re_rand_paths,
                alice_r1cs_proof,
            );

            println!(
                "reveal_asset_id={reveal_asset_id}: Alice split multi-asset: proving time = {:?}, proof size = {} bytes",
                alice_proving_time,
                alice_split_proof.compressed_size()
            );

            // ── Bob's split multi-asset proof ────────────────────────────────

            let mut bob_split_builder_1 = AccountStateTransitionSplitProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new(
                bob_account_1.clone(),
                bob_account_1_updated.clone(),
                bob_account_1_updated_comm,
                bob_nonce,
            );
            bob_split_builder_1.add_receive_affirmation((
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            let mut bob_split_builder_2 = AccountStateTransitionSplitProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::new(
                bob_account_2.clone(),
                bob_account_2_updated.clone(),
                bob_account_2_updated_comm,
                bob_nonce,
            );
            bob_split_builder_2.add_send_affirmation(
                bob_send_amount,
                (
                    leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                    leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                ),
            );

            let start = Instant::now();
            let (bob_host_protocol, mut bob_even_prover, bob_odd_prover) =
                MultiAssetStateTransitionHostProtocol::<
                    L,
                    M,
                    _,
                    _,
                    PallasParameters,
                    VestaParameters,
                >::init::<_, PallasParams, VestaParams>(
                    &mut rng,
                    vec![bob_split_builder_1, bob_split_builder_2],
                    vec![bob_leaf_path],
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                    &[&[], &[k_amount_bob]],
                    &[&k_asset_ids_bob_1[..], &k_asset_ids_bob_2[..]],
                )
                .unwrap();

            let bob_challenge = {
                let transcript = bob_even_prover.transcript();
                transcript.challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
            };

            let bob_nullifier_1 = bob_host_protocol.nullifiers[0];
            let bob_nullifier_2 = bob_host_protocol.nullifiers[1];
            let bob_re_rand_leaf_1 = bob_host_protocol.rerandomized_leaves[0];
            let bob_re_rand_leaf_2 = bob_host_protocol.rerandomized_leaves[1];
            let bob_auth_rerand_1 = bob_host_protocol.protocols[0].auth_rerandomization();
            let bob_auth_rerand_2 = bob_host_protocol.protocols[1].auth_rerandomization();
            let bob_auth_rand_new_comm_1 = bob_host_protocol.protocols[0].auth_rand_new_comm();
            let bob_auth_rand_new_comm_2 = bob_host_protocol.protocols[1].auth_rand_new_comm();

            let mut bob_auth_transcript = MerlinTranscript::new(AUTH_TXN_LABEL);

            let bob_auth_proof_1 = AuthProofAffirmation::new_with_given_transcript(
                &mut rng,
                sk_bob_scalar,
                sk_bob_e_scalar,
                bob_auth_rerand_1,
                bob_auth_rand_new_comm_1,
                vec![],
                k_asset_ids_bob_1.clone(),
                vec![LegProverConfig {
                    encryption: leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Receiver(
                        leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                    ),
                    has_balance_changed: false,
                }],
                &bob_re_rand_leaf_1,
                &bob_account_1_updated_comm.0,
                bob_nullifier_1,
                bob_nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                &mut bob_auth_transcript,
            )
            .unwrap();

            let bob_auth_proof_2 = AuthProofAffirmation::new_with_given_transcript(
                &mut rng,
                sk_bob_scalar,
                sk_bob_e_scalar,
                bob_auth_rerand_2,
                bob_auth_rand_new_comm_2,
                vec![k_amount_bob],
                k_asset_ids_bob_2.clone(),
                vec![LegProverConfig {
                    encryption: leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::Sender(
                        leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                    ),
                    has_balance_changed: true,
                }],
                &bob_re_rand_leaf_2,
                &bob_account_2_updated_comm.0,
                bob_nullifier_2,
                bob_nonce,
                account_comm_key.sk_gen(),
                account_comm_key.sk_enc_gen(),
                b_blinding,
                enc_gen,
                &mut bob_auth_transcript,
            )
            .unwrap();

            let (bob_account_data, bob_re_rand_paths, bob_r1cs_proof) = bob_host_protocol
                .gen_proof::<_, PallasParams, VestaParams>(
                    &bob_challenge,
                    bob_even_prover,
                    bob_odd_prover,
                    &account_tree_params,
                    &mut rng,
                )
                .unwrap();
            let bob_proving_time = start.elapsed();

            let bob_split_proof = MultiAssetStateTransitionSplitProof::assemble(
                bob_account_data,
                vec![bob_auth_proof_1, bob_auth_proof_2],
                bob_re_rand_paths,
                bob_r1cs_proof,
            );

            println!(
                "reveal_asset_id={reveal_asset_id}: Bob split multi-asset: proving time = {:?}, proof size = {} bytes",
                bob_proving_time,
                bob_split_proof.compressed_size()
            );

            // ── Verify Alice's proof ─────────────────────────────────────────

            let start = Instant::now();

            let mut alice_verifier_1a = AccountStateTransitionProofVerifier::init(
                alice_account_1_updated_comm,
                alice_nullifier_1,
                alice_nonce,
            );
            alice_verifier_1a.add_send_affirmation((
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ));

            let mut alice_verifier_2a = AccountStateTransitionProofVerifier::init(
                alice_account_2_updated_comm,
                alice_nullifier_2,
                alice_nonce,
            );
            alice_verifier_2a.add_receive_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            let (
                alice_split_verifiers,
                alice_rerand_leaves,
                mut alice_even_verifier,
                alice_odd_verifier,
            ) = alice_split_proof
                .challenge_contribution::<PallasParams, VestaParams>(
                    &[alice_verifier_1a, alice_verifier_2a],
                    &account_tree_root,
                    &account_tree_params,
                    &account_comm_key,
                    enc_gen,
                )
                .unwrap();

            let alice_challenge_v = alice_even_verifier
                .transcript()
                .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

            let mut alice_auth_verify_transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
            alice_split_proof.account_proofs[0]
                .common_proof
                .auth_proof
                .verify_with_given_transcript(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Sender(
                            leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                        ),
                        has_balance_decreased: Some(true),
                        has_counter_decreased: Some(true),
                    }],
                    &alice_rerand_leaves[0],
                    &alice_account_1_updated_comm.0,
                    alice_nullifier_1,
                    alice_nonce,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    &mut alice_auth_verify_transcript,
                    None,
                )
                .unwrap();

            alice_split_proof.account_proofs[1]
                .common_proof
                .auth_proof
                .verify_with_given_transcript(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(
                            leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                        ),
                        has_balance_decreased: None,
                        has_counter_decreased: Some(false),
                    }],
                    &alice_rerand_leaves[1],
                    &alice_account_2_updated_comm.0,
                    alice_nullifier_2,
                    alice_nonce,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    &mut alice_auth_verify_transcript,
                    None,
                )
                .unwrap();

            let mut alice_verifier_1b = AccountStateTransitionProofVerifier::init(
                alice_account_1_updated_comm,
                alice_nullifier_1,
                alice_nonce,
            );
            alice_verifier_1b.add_send_affirmation((
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ));

            let mut alice_verifier_2b = AccountStateTransitionProofVerifier::init(
                alice_account_2_updated_comm,
                alice_nullifier_2,
                alice_nonce,
            );
            alice_verifier_2b.add_receive_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            alice_split_proof
                .verify::<_, PallasParams, VestaParams>(
                    vec![alice_verifier_1b, alice_verifier_2b],
                    alice_split_verifiers,
                    &alice_challenge_v,
                    &account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    alice_even_verifier,
                    alice_odd_verifier,
                    &mut rng,
                    None,
                )
                .unwrap();

            let alice_verification_time = start.elapsed();
            println!(
                "reveal_asset_id={reveal_asset_id}: Alice split multi-asset: verification time = {:?}",
                alice_verification_time
            );

            // ── Verify Bob's proof ───────────────────────────────────────────

            let start = Instant::now();

            let mut bob_verifier_1a = AccountStateTransitionProofVerifier::init(
                bob_account_1_updated_comm,
                bob_nullifier_1,
                bob_nonce,
            );
            bob_verifier_1a.add_receive_affirmation((
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            let mut bob_verifier_2a = AccountStateTransitionProofVerifier::init(
                bob_account_2_updated_comm,
                bob_nullifier_2,
                bob_nonce,
            );
            bob_verifier_2a.add_send_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ));

            let (bob_split_verifiers, bob_rerand_leaves, mut bob_even_verifier, bob_odd_verifier) =
                bob_split_proof
                    .challenge_contribution::<PallasParams, VestaParams>(
                        &[bob_verifier_1a, bob_verifier_2a],
                        &account_tree_root,
                        &account_tree_params,
                        &account_comm_key,
                        enc_gen,
                    )
                    .unwrap();

            let bob_challenge_v = bob_even_verifier
                .transcript()
                .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

            let mut bob_auth_verify_transcript = MerlinTranscript::new(AUTH_TXN_LABEL);
            bob_split_proof.account_proofs[0]
                .common_proof
                .auth_proof
                .verify_with_given_transcript(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Receiver(
                            leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
                        ),
                        has_balance_decreased: None,
                        has_counter_decreased: Some(false),
                    }],
                    &bob_rerand_leaves[0],
                    &bob_account_1_updated_comm.0,
                    bob_nullifier_1,
                    bob_nonce,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    &mut bob_auth_verify_transcript,
                    None,
                )
                .unwrap();

            bob_split_proof.account_proofs[1]
                .common_proof
                .auth_proof
                .verify_with_given_transcript(
                    vec![LegVerifierConfig {
                        encryption: leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::Sender(
                            leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
                        ),
                        has_balance_decreased: Some(true),
                        has_counter_decreased: Some(true),
                    }],
                    &bob_rerand_leaves[1],
                    &bob_account_2_updated_comm.0,
                    bob_nullifier_2,
                    bob_nonce,
                    account_comm_key.sk_gen(),
                    account_comm_key.sk_enc_gen(),
                    b_blinding,
                    enc_gen,
                    &mut bob_auth_verify_transcript,
                    None,
                )
                .unwrap();

            let mut bob_verifier_1b = AccountStateTransitionProofVerifier::init(
                bob_account_1_updated_comm,
                bob_nullifier_1,
                bob_nonce,
            );
            bob_verifier_1b.add_receive_affirmation((
                leg_enc_1.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_1.leg_enc_core_and_eph_keys.eph_pk_r.clone(),
            ));

            let mut bob_verifier_2b = AccountStateTransitionProofVerifier::init(
                bob_account_2_updated_comm,
                bob_nullifier_2,
                bob_nonce,
            );
            bob_verifier_2b.add_send_affirmation((
                leg_enc_2.leg_enc_core_and_eph_keys.core.clone(),
                leg_enc_2.leg_enc_core_and_eph_keys.eph_pk_s.clone(),
            ));

            bob_split_proof
                .verify::<_, PallasParams, VestaParams>(
                    vec![bob_verifier_1b, bob_verifier_2b],
                    bob_split_verifiers,
                    &bob_challenge_v,
                    &account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    bob_even_verifier,
                    bob_odd_verifier,
                    &mut rng,
                    None,
                )
                .unwrap();

            let bob_verification_time = start.elapsed();
            println!(
                "reveal_asset_id={reveal_asset_id}: Bob split multi-asset: verification time = {:?}",
                bob_verification_time
            );
        };

        test_with_config(false);
        test_with_config(true);
    }
}
