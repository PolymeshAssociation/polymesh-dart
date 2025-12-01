use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, BalanceChangeConfig,
    BalanceChangeProof, BalanceChangeProver, CommonStateChangeProof, CommonStateChangeProver,
    LegProverConfig, LegVerifierConfig, StateChangeVerifier,
};
use crate::leg::{LegEncryption, LegEncryptionRandomness};
use crate::util::{
    BPProof, add_verification_tuples_to_rmc, get_verification_tuples_with_rng, prove_with_rng,
    verify_given_verification_tuples,
};
use crate::{Error, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::marker::PhantomData;
use ark_std::{format, string::ToString, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::Balance;
use rand_core::CryptoRngCore;

/// Combined proof for multi-leg state transitions
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountStateTransitionProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
    pub balance_proof: Option<BalanceChangeProof<F0, G0>>,
}

pub struct AccountStateTransitionProofBuilder<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    legs: Vec<LegProverConfig<F0, G0>>,
    balance_changes: Vec<BalanceChangeConfig<F0, G0>>,
    net_counter_change: i32,
    account: AccountState<Affine<G0>>,
    updated_account: AccountState<Affine<G0>>,
    updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    nonce: Vec<u8>,
    marker: PhantomData<G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AccountStateTransitionProofBuilder<L, F0, F1, G0, G1>
{
    pub fn init(
        account: AccountState<Affine<G0>>,
        updated_account: AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nonce: &[u8],
    ) -> Self {
        Self {
            legs: Vec::new(),
            balance_changes: Vec::new(),
            net_counter_change: 0,
            account,
            updated_account,
            updated_account_commitment,
            nonce: nonce.to_vec(),
            marker: PhantomData,
        }
    }

    pub fn nonce(&self) -> &[u8] {
        &self.nonce
    }

    pub fn updated_account_commitment(&self) -> AccountStateCommitment<Affine<G0>> {
        self.updated_account_commitment
    }

    pub fn add_send_affirmation(
        &mut self,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        let ct_amount = leg_enc.ct_amount;
        let r_3 = leg_enc_rand.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: true,
            has_balance_changed: true,
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            r_3,
            has_balance_decreased: true,
        });

        self.net_counter_change += 1;
    }

    pub fn add_receive_affirmation(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: false,
            has_balance_changed: false,
        });

        self.net_counter_change += 1;
    }

    pub fn add_claim_received(
        &mut self,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        let ct_amount = leg_enc.ct_amount;
        let r_3 = leg_enc_rand.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: false,
            has_balance_changed: true,
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            r_3,
            has_balance_decreased: false,
        });

        self.net_counter_change -= 1;
    }

    pub fn add_sender_counter_update(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: true,
            has_balance_changed: false,
        });

        self.net_counter_change -= 1;
    }

    pub fn add_sender_reverse(
        &mut self,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        let ct_amount = leg_enc.ct_amount;
        let r_3 = leg_enc_rand.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: true,
            has_balance_changed: true,
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            r_3,
            has_balance_decreased: false,
        });

        self.net_counter_change -= 1;
    }

    pub fn add_receiver_reverse(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: false,
            has_balance_changed: false,
        });

        self.net_counter_change -= 1;
    }

    pub fn add_irreversible_send(
        &mut self,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        let ct_amount = leg_enc.ct_amount;
        let r_3 = leg_enc_rand.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: true,
            has_balance_changed: true,
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            r_3,
            has_balance_decreased: true,
        });
    }

    pub fn add_irreversible_receive(
        &mut self,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<F0>,
    ) {
        let ct_amount = leg_enc.ct_amount;
        let r_3 = leg_enc_rand.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc,
            randomness: leg_enc_rand,
            is_sender: false,
            has_balance_changed: true,
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            r_3,
            has_balance_decreased: false,
        });
    }

    pub fn finalize<R: CryptoRngCore>(
        self,
        rng: &mut R,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(AccountStateTransitionProof<L, F0, F1, G0, G1>, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = self.finalize_with_given_prover(
            rng,
            leaf_path,
            root,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )?;

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params, rng)?;

        proof.common_proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((proof, nullifier))
    }

    pub fn finalize_with_given_prover<'a, R: CryptoRngCore>(
        self,
        rng: &mut R,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(AccountStateTransitionProof<L, F0, F1, G0, G1>, Affine<G0>)> {
        self.pre_finalize_checks()?;

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            self.legs.clone(),
            &self.account,
            &self.updated_account,
            self.updated_account_commitment,
            leaf_path,
            root,
            &self.nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        self.generate_proof_given_common_prover(
            rng,
            common_prover,
            account_tree_params,
            enc_key_gen,
            enc_gen,
            even_prover,
        )
    }

    /// Creates a proof when the account leaf has already been re-randomized externally.
    /// This is useful for batched proving when proving multiple account paths at once.
    pub fn finalize_with_given_prover_with_rerandomized_leaf<'a, R: CryptoRngCore>(
        self,
        rng: &mut R,
        leaf_rerandomization: F0,
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
    ) -> Result<(AccountStateTransitionProof<L, F0, F1, G0, G1>, Affine<G0>)> {
        self.pre_finalize_checks()?;
        let common_prover = CommonStateChangeProver::init_with_given_prover_with_rerandomized_leaf(
            rng,
            self.legs.clone(),
            &self.account,
            &self.updated_account,
            self.updated_account_commitment,
            leaf_rerandomization,
            &self.nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
        )?;

        self.generate_proof_given_common_prover(
            rng,
            common_prover,
            account_tree_params,
            enc_key_gen,
            enc_gen,
            even_prover,
        )
    }

    fn generate_proof_given_common_prover<'a, R: CryptoRngCore>(
        self,
        rng: &mut R,
        common_prover: CommonStateChangeProver<'a, L, F0, F1, G0, G1>,
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
    ) -> Result<(AccountStateTransitionProof<L, F0, F1, G0, G1>, Affine<G0>)> {
        let nullifier = common_prover.nullifier;
        let has_balance_changed = !self.balance_changes.is_empty();

        let balance_prover = if has_balance_changed {
            Some(BalanceChangeProver::init(
                rng,
                self.balance_changes,
                &self.account,
                &self.updated_account,
                common_prover.old_balance_blinding,
                common_prover.new_balance_blinding,
                even_prover,
                &account_tree_params.even_parameters.pc_gens,
                &account_tree_params.even_parameters.bp_gens,
                enc_key_gen,
                enc_gen,
            )?)
        } else {
            None
        };

        let transcript = even_prover.transcript();
        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof = common_prover.generate_sigma_responses(
            &self.account,
            &self.updated_account,
            &challenge,
        )?;

        let balance_proof = balance_prover
            .map(|bp| bp.gen_proof(&challenge))
            .transpose()?;

        Ok((
            AccountStateTransitionProof {
                common_proof,
                balance_proof,
            },
            nullifier,
        ))
    }

    fn pre_finalize_checks(&self) -> Result<()> {
        #[cfg(feature = "ignore_prover_input_sanitation")]
        {
            return Ok(());
        }

        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        {
            if self.legs.is_empty() {
                return Err(Error::ProofGenerationError(
                    "No legs added to the builder".to_string(),
                ));
            }

            let expected_counter =
                (self.account.counter as i64 + self.net_counter_change as i64) as u64;
            if self.updated_account.counter != expected_counter {
                return Err(Error::ProofGenerationError(format!(
                    "Counter mismatch: expected {}, got {}",
                    expected_counter, self.updated_account.counter
                )));
            }
            Ok(())
        }
    }
}

pub struct AccountStateTransitionProofVerifier<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    legs: Vec<LegVerifierConfig<G0>>,
    net_counter_change: i32,
    updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    nullifier: Affine<G0>,
    nonce: Vec<u8>,
    marker: PhantomData<G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>
{
    pub fn init(
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
    ) -> Self {
        Self {
            legs: Vec::new(),
            net_counter_change: 0,
            updated_account_commitment,
            nullifier,
            nonce: nonce.to_vec(),
            marker: PhantomData,
        }
    }

    pub fn add_send_affirmation(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: true,
            has_balance_decreased: Some(true),
            has_counter_decreased: Some(false),
        });
        self.net_counter_change += 1;
    }

    pub fn add_receive_affirmation(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: false,
            has_balance_decreased: None,
            has_counter_decreased: Some(false),
        });
        self.net_counter_change += 1;
    }

    pub fn add_claim_received(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: false,
            has_balance_decreased: Some(false),
            has_counter_decreased: Some(true),
        });
        self.net_counter_change -= 1;
    }

    pub fn add_sender_counter_update(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: true,
            has_balance_decreased: None,
            has_counter_decreased: Some(true),
        });
        self.net_counter_change -= 1;
    }

    pub fn add_sender_reverse(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: true,
            has_balance_decreased: Some(false),
            has_counter_decreased: Some(true),
        });
        self.net_counter_change -= 1;
    }

    pub fn add_receiver_reverse(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: false,
            has_balance_decreased: None,
            has_counter_decreased: Some(true),
        });
        self.net_counter_change -= 1;
    }

    pub fn add_irreversible_send(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: true,
            has_balance_decreased: Some(true),
            has_counter_decreased: None,
        });
    }

    pub fn add_irreversible_receive(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc,
            is_sender: false,
            has_balance_decreased: Some(false),
            has_counter_decreased: None,
        });
    }

    pub fn verify<R: CryptoRngCore>(
        self,
        rng: &mut R,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
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

        let (even_tuple, odd_tuple) = self.verify_and_return_tuples(
            proof,
            root,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
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

    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        self.pre_verify_checks(proof)?;

        let mut verifier = StateChangeVerifier::init(
            &proof.common_proof,
            self.legs.clone(),
            root,
            self.updated_account_commitment,
            self.nullifier,
            &self.nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        let mut even_verifier = verifier.even_verifier.take().unwrap();
        let odd_verifier = verifier.odd_verifier.take().unwrap();

        self.verify_sigma_protocols_given_state_change_verifier(
            proof,
            verifier,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            rmc,
        )?;

        let r1cs_proof =
            proof.common_proof.r1cs_proof.as_ref().ok_or_else(|| {
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

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        self.pre_verify_checks(proof)?;

        let verifier = StateChangeVerifier::init_with_given_verifier(
            &proof.common_proof,
            self.legs.clone(),
            root,
            self.updated_account_commitment,
            self.nullifier,
            &self.nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        self.verify_sigma_protocols_given_state_change_verifier(
            proof,
            verifier,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            rmc,
        )
    }

    /// Verifies the proof when the account leaf has already been re-randomized externally.
    /// This is useful for batched verification when verifying multiple account paths at once.
    /// `rerandomized_leaf` - The re-randomized leaf obtained from external batched curve tree operations.
    pub fn enforce_constraints_and_verify_only_sigma_protocols_with_rerandomized_leaf(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        rerandomized_leaf: Affine<G0>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        self.pre_verify_checks(proof)?;

        let verifier = StateChangeVerifier::init_with_given_verifier_with_rerandomized_leaf(
            &proof.common_proof,
            self.legs.clone(),
            self.updated_account_commitment,
            self.nullifier,
            rerandomized_leaf,
            &self.nonce,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
        )?;

        self.verify_sigma_protocols_given_state_change_verifier(
            proof,
            verifier,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            rmc,
        )
    }

    fn verify_sigma_protocols_given_state_change_verifier(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        mut verifier: StateChangeVerifier<L, F0, F1, G0, G1>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        if let Some(balance_proof) = &proof.balance_proof {
            let ct_amounts: Vec<Affine<G0>> = self
                .legs
                .iter()
                .filter(|l| l.has_balance_decreased.is_some())
                .map(|l| l.encryption.ct_amount)
                .collect();

            verifier.init_balance_change_verification_with_given_verifier(
                balance_proof,
                &ct_amounts,
                enc_key_gen,
                enc_gen,
                even_verifier,
            )?;
        }

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let leg_encs: Vec<LegEncryption<Affine<G0>>> =
            self.legs.iter().map(|l| l.encryption.clone()).collect();

        verifier.verify_sigma_protocols(
            &proof.common_proof,
            proof.balance_proof.as_ref(),
            &challenge,
            leg_encs,
            self.updated_account_commitment,
            self.nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }

    fn pre_verify_checks(
        &self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
    ) -> Result<()> {
        if self.legs.is_empty() {
            return Err(Error::ProofVerificationError(
                "No legs added to the verifier".to_string(),
            ));
        }

        let num_legs_with_balance_change = self
            .legs
            .iter()
            .filter(|l| l.has_balance_decreased.is_some())
            .count();
        if num_legs_with_balance_change > 0 {
            if let Some(balance_proof) = &proof.balance_proof {
                if balance_proof.resp_leg_amount.len() != num_legs_with_balance_change {
                    return Err(Error::ProofVerificationError(format!(
                        "{num_legs_with_balance_change} legs with balance change but balance change proof for {} legs provided",
                        balance_proof.resp_leg_amount.len()
                    )));
                }
            } else {
                return Err(Error::ProofVerificationError(format!(
                    "{num_legs_with_balance_change} legs with balance change but no balance change proof provided"
                )));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account::AccountStateBuilder;
    use crate::account::tests::{get_tree_with_account_comm, setup_gens};
    use crate::account_registration::tests::new_account;
    use crate::leg::Leg;
    use crate::leg::tests::setup_keys;
    use crate::util::{batch_verify_bp, verify_with_rng};
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::CurveTree;
    use rand::thread_rng;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;

    type PallasFr = ark_pallas::Fr;

    #[test]

    fn test_multi_leg_two_senders_one_receiver() {
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"test");

        // Setup keys for Alice, Bob, Carol, and auditor
        let (
            ((_sk_alice, pk_alice), (_, pk_alice_e)),
            ((_sk_bob, pk_bob), (_, pk_bob_e)),
            ((sk_carol, pk_carol), (_, pk_carol_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_send_amount = 100u64;
        let bob_send_amount = 200u64;

        // Create legs
        let leg_1 = Leg::new(
            pk_alice.0,
            pk_carol.0,
            vec![(true, pk_auditor_e.0)],
            alice_send_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_carol_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_2 = Leg::new(
            pk_bob.0,
            pk_carol.0,
            vec![(true, pk_auditor_e.0)],
            bob_send_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_bob_e.0, pk_carol_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create Carol's account
        let carol_id = PallasFr::rand(&mut rng);
        let (mut carol_account, _, _) = new_account(&mut rng, asset_id, sk_carol, carol_id);
        carol_account.balance = 500;

        let account_tree = get_tree_with_account_comm::<L>(
            &carol_account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let carol_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root = account_tree.root_node();
        let nonce_1 = b"carol_nonce_1";
        let nonce_2 = b"carol_nonce_2";

        // Carol receives from both:
        let mut builder = AccountStateBuilder::init(carol_account.clone());
        builder.update_for_receive();
        builder.update_for_receive();
        let carol_receives = builder.finalize();
        let carol_receives_comm = carol_receives.commit(account_comm_key.clone()).unwrap();

        // Carol creates multi-leg proof for receive affirmations
        let mut carol_builder_1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                carol_account.clone(),
                carol_receives.clone(),
                carol_receives_comm,
                nonce_1,
            );
        carol_builder_1.add_receive_affirmation(leg_enc_1.clone(), leg_enc_rand_1.clone());
        carol_builder_1.add_receive_affirmation(leg_enc_2.clone(), leg_enc_rand_2.clone());

        let start = Instant::now();
        let (carol_proof_1, carol_nullifier_1) = carol_builder_1
            .finalize(
                &mut rng,
                carol_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time_1 = start.elapsed();

        // Verify Carol's first proof
        let mut carol_verifier_1 = AccountStateTransitionProofVerifier::init(
            carol_receives_comm,
            carol_nullifier_1,
            nonce_1,
        );
        carol_verifier_1.add_receive_affirmation(leg_enc_1.clone());
        carol_verifier_1.add_receive_affirmation(leg_enc_2.clone());

        let start = Instant::now();
        carol_verifier_1
            .verify(
                &mut rng,
                &carol_proof_1,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time_1 = start.elapsed();
        let proof_size_1 = carol_proof_1.compressed_size();
        println!(
            "Carol proof 1 (2 receive affirmations): proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time_1, verification_time_1, proof_size_1
        );

        // Now Carol claims from both
        let mut builder = AccountStateBuilder::init(carol_receives.clone());
        builder
            .update_for_claiming_received(alice_send_amount)
            .unwrap();
        builder
            .update_for_claiming_received(bob_send_amount)
            .unwrap();
        let carol_final = builder.finalize();
        let carol_final_comm = carol_final.commit(account_comm_key.clone()).unwrap();

        // Update the tree with Carol's new state after receives
        let account_tree_2 = get_tree_with_account_comm::<L>(
            &carol_receives,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();
        let carol_leaf_path_2 = account_tree_2.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root_2 = account_tree_2.root_node();

        // Carol creates multi-leg proof for claims
        let mut carol_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                carol_receives.clone(),
                carol_final.clone(),
                carol_final_comm,
                nonce_2,
            );
        carol_builder_2.add_claim_received(
            alice_send_amount,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
        );
        carol_builder_2.add_claim_received(
            bob_send_amount,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
        );

        let start = Instant::now();
        let (carol_proof_2, carol_nullifier_2) = carol_builder_2
            .finalize(
                &mut rng,
                carol_leaf_path_2.clone(),
                &account_tree_root_2,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time_2 = start.elapsed();

        // Verify Carol's second proof
        let mut carol_verifier_2 =
            AccountStateTransitionProofVerifier::init(carol_final_comm, carol_nullifier_2, nonce_2);
        carol_verifier_2.add_claim_received(leg_enc_1.clone());
        carol_verifier_2.add_claim_received(leg_enc_2.clone());

        let start = Instant::now();
        carol_verifier_2
            .verify(
                &mut rng,
                &carol_proof_2,
                &account_tree_root_2,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time_2 = start.elapsed();
        let proof_size_2 = carol_proof_2.compressed_size();
        println!(
            "Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time_2, verification_time_2, proof_size_2
        );
    }

    #[test]
    fn test_multi_leg_sender_and_receiver() {
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"test");

        // Setup keys for Alice, Bob, Carol, and auditor
        let (
            ((sk_alice, pk_alice), (_, pk_alice_e)),
            ((_, pk_bob), (_, pk_bob_e)),
            ((_, pk_carol), (_, pk_carol_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_to_bob_amount = 100u64;
        let carol_to_alice_amount = 150u64;

        // Create legs
        let leg_1 = Leg::new(
            pk_alice.0,
            pk_bob.0,
            vec![(true, pk_auditor_e.0)],
            alice_to_bob_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_bob_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_2 = Leg::new(
            pk_carol.0,
            pk_alice.0,
            vec![(true, pk_auditor_e.0)],
            carol_to_alice_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_carol_e.0, pk_alice_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create Alice's account
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account, _, _) = new_account(&mut rng, asset_id, sk_alice, alice_id);
        alice_account.balance = 1000;

        // Alice sends and receives
        let mut builder = AccountStateBuilder::init(alice_account.clone());
        builder.update_for_send(alice_to_bob_amount).unwrap();
        builder.update_for_receive();
        let alice_updated = builder.finalize();
        let alice_updated_comm = alice_updated.commit(account_comm_key.clone()).unwrap();

        // Create account tree with both alice_account and alice_updated commitments.
        // Note: This is just for testing. In practice, alice_updated would be inserted later after the first proof is verified on-chain.
        let alice_account_comm = alice_account.commit(account_comm_key.clone()).unwrap();
        let account_comms = vec![alice_account_comm.0, alice_updated_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(4),
        );
        let account_tree_root = account_tree.root_node();

        let alice_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let nonce = b"alice_nonce";

        // Alice creates multi-leg proof 1
        let mut alice_builder =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account.clone(),
                alice_updated.clone(),
                alice_updated_comm,
                nonce,
            );
        alice_builder.add_send_affirmation(
            alice_to_bob_amount,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
        );
        alice_builder.add_receive_affirmation(leg_enc_2.clone(), leg_enc_rand_2.clone());

        let start = Instant::now();
        let (alice_proof, alice_nullifier) = alice_builder
            .finalize(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time_1 = start.elapsed();

        // Verify Alice's proof 1
        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_send_affirmation(leg_enc_1.clone());
        alice_verifier.add_receive_affirmation(leg_enc_2.clone());

        let start = Instant::now();
        alice_verifier
            .verify(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time_1 = start.elapsed();
        let proof_size_1 = alice_proof.compressed_size();
        println!(
            "Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time_1, verification_time_1, proof_size_1
        );

        // Get path for alice_updated (at index 1 in the tree)
        let alice_leaf_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();
        let nonce_2 = b"alice_nonce_2";

        // Alice does proof 2: claim received amount and update sender counter
        let mut builder = AccountStateBuilder::init(alice_updated.clone());
        builder
            .update_for_claiming_received(carol_to_alice_amount)
            .unwrap();
        builder.update_for_decreasing_counter(None).unwrap();
        let alice_final = builder.finalize();
        let alice_final_comm = alice_final.commit(account_comm_key.clone()).unwrap();

        let mut alice_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_updated.clone(),
                alice_final.clone(),
                alice_final_comm,
                nonce_2,
            );
        alice_builder_2.add_claim_received(
            carol_to_alice_amount,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
        );
        alice_builder_2.add_sender_counter_update(leg_enc_1.clone(), leg_enc_rand_1.clone());

        let start = Instant::now();
        let (alice_proof_2, alice_nullifier_2) = alice_builder_2
            .finalize(
                &mut rng,
                alice_leaf_path_2.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time_2 = start.elapsed();

        // Verify Alice's proof 2
        let mut alice_verifier_2 =
            AccountStateTransitionProofVerifier::init(alice_final_comm, alice_nullifier_2, nonce_2);
        alice_verifier_2.add_claim_received(leg_enc_2.clone());
        alice_verifier_2.add_sender_counter_update(leg_enc_1.clone());

        let start = Instant::now();
        alice_verifier_2
            .verify(
                &mut rng,
                &alice_proof_2,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time_2 = start.elapsed();
        let proof_size_2 = alice_proof_2.compressed_size();
        println!(
            "Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time_2, verification_time_2, proof_size_2
        );

        // Test batch verification using verify_and_return_tuples
        let start = Instant::now();

        let mut batch_verifier_1 =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        batch_verifier_1.add_send_affirmation(leg_enc_1.clone());
        batch_verifier_1.add_receive_affirmation(leg_enc_2.clone());
        let (even_tuple_1, odd_tuple_1) = batch_verifier_1
            .verify_and_return_tuples(
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let mut batch_verifier_2 =
            AccountStateTransitionProofVerifier::init(alice_final_comm, alice_nullifier_2, nonce_2);
        batch_verifier_2.add_claim_received(leg_enc_2.clone());
        batch_verifier_2.add_sender_counter_update(leg_enc_1.clone());
        let (even_tuple_2, odd_tuple_2) = batch_verifier_2
            .verify_and_return_tuples(
                &alice_proof_2,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        batch_verify_bp(
            vec![even_tuple_1, even_tuple_2],
            vec![odd_tuple_1, odd_tuple_2],
            &account_tree_params,
        )
        .unwrap();

        let batch_verification_time = start.elapsed();
        println!(
            "Batch verification time for 2 proofs = {:?}",
            batch_verification_time
        );
    }

    #[test]
    fn test_send_receive_and_reverse() {
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"test");

        // Setup keys for Alice, Bob, Carol, Dave, and auditor
        let (
            ((sk_alice, pk_alice), (_, pk_alice_e)),
            ((_, pk_bob), (_, pk_bob_e)),
            ((_, pk_carol), (_, pk_carol_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let ((_, pk_dave), (_, pk_dave_e)) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen).0;
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_to_bob_amount = 100u64; // Leg 1: Alice sends to Bob (send affirmation)
        let carol_to_alice_amount = 150u64; // Leg 2: Carol sends to Alice (receive affirmation)
        let alice_to_dave_amount = 50u64; // Leg 3: Alice sends to Dave but reverses (sender reverse)
        let bob_to_alice_amount = 75u64; // Leg 4: Bob sends to Alice but Alice reverses (receiver counter update)

        // Create legs
        let leg_1 = Leg::new(
            pk_alice.0,
            pk_bob.0,
            vec![(true, pk_auditor_e.0)],
            alice_to_bob_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_bob_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_2 = Leg::new(
            pk_carol.0,
            pk_alice.0,
            vec![(true, pk_auditor_e.0)],
            carol_to_alice_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_carol_e.0, pk_alice_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_3 = Leg::new(
            pk_alice.0,
            pk_dave.0,
            vec![(true, pk_auditor_e.0)],
            alice_to_dave_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_3, leg_enc_rand_3) = leg_3
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_dave_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_4 = Leg::new(
            pk_bob.0,
            pk_alice.0,
            vec![(true, pk_auditor_e.0)],
            bob_to_alice_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_4, leg_enc_rand_4) = leg_4
            .encrypt::<_, Blake2b512>(&mut rng, pk_bob_e.0, pk_alice_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create Alice's account
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account, _, _) = new_account(&mut rng, asset_id, sk_alice, alice_id);
        alice_account.balance = 1000;

        let account_tree = get_tree_with_account_comm::<L>(
            &alice_account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let alice_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root = account_tree.root_node();
        let nonce = b"alice_nonce_4ops";

        // Alice does 4 operations in one proof:
        // 1. Send affirmation to Bob: balance -100, counter +1
        // 2. Receive affirmation from Carol: balance unchanged, counter +1
        // 3. Sender reverse (to Dave): balance +50 (gets back), counter -1
        // 4. Receiver counter update (from Bob): counter -1
        // Net: balance = 1000 - 100 + 50 = 950, counter = 0 + 1 + 1 - 1 - 1 = 0
        let mut builder = AccountStateBuilder::init(alice_account.clone());
        builder.update_for_send(alice_to_bob_amount).unwrap();
        builder.update_for_receive();
        builder
            .update_for_reversing_send(alice_to_dave_amount)
            .unwrap();
        builder.update_for_decreasing_counter(None).unwrap();
        let alice_updated = builder.finalize();
        let alice_updated_comm = alice_updated.commit(account_comm_key.clone()).unwrap();

        let mut alice_builder =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account.clone(),
                alice_updated.clone(),
                alice_updated_comm,
                nonce,
            );
        alice_builder.add_send_affirmation(
            alice_to_bob_amount,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
        );
        alice_builder.add_receive_affirmation(leg_enc_2.clone(), leg_enc_rand_2.clone());
        alice_builder.add_sender_reverse(
            alice_to_dave_amount,
            leg_enc_3.clone(),
            leg_enc_rand_3.clone(),
        );
        alice_builder.add_receiver_reverse(leg_enc_4.clone(), leg_enc_rand_4.clone());

        let start = Instant::now();
        let (alice_proof, alice_nullifier) = alice_builder
            .finalize(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time = start.elapsed();

        // Verify Alice's proof
        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_send_affirmation(leg_enc_1.clone());
        alice_verifier.add_receive_affirmation(leg_enc_2.clone());
        alice_verifier.add_sender_reverse(leg_enc_3.clone());
        alice_verifier.add_receiver_reverse(leg_enc_4.clone());

        let start = Instant::now();
        alice_verifier
            .verify(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time = start.elapsed();
        let proof_size = alice_proof.compressed_size();
        println!(
            "Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time, verification_time, proof_size
        );
    }

    #[test]
    fn test_multi_leg_irreversible_operations() {
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"test");

        // Setup keys for Alice, Bob, Carol, and auditor
        let (
            ((sk_alice, pk_alice), (_, pk_alice_e)),
            ((_, pk_bob), (_, pk_bob_e)),
            ((_, pk_carol), (_, pk_carol_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_to_bob_amount = 200u64; // Leg 1: Alice irreversibly sends to Bob
        let carol_to_alice_amount = 300u64; // Leg 2: Carol irreversibly sends to Alice

        // Create legs
        let leg_1 = Leg::new(
            pk_alice.0,
            pk_bob.0,
            vec![(true, pk_auditor_e.0)],
            alice_to_bob_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_bob_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_2 = Leg::new(
            pk_carol.0,
            pk_alice.0,
            vec![(true, pk_auditor_e.0)],
            carol_to_alice_amount,
            asset_id,
        )
        .unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_carol_e.0, pk_alice_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create Alice's account
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account, _, _) = new_account(&mut rng, asset_id, sk_alice, alice_id);
        alice_account.balance = 1000;

        let account_tree = get_tree_with_account_comm::<L>(
            &alice_account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let alice_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root = account_tree.root_node();
        let nonce = b"alice_nonce_irreversible";

        // Alice does 2 irreversible operations in one proof:
        let mut builder = AccountStateBuilder::init(alice_account.clone());
        builder
            .update_for_irreversible_send(alice_to_bob_amount)
            .unwrap();
        builder
            .update_for_irreversible_receive(carol_to_alice_amount)
            .unwrap();
        let alice_updated = builder.finalize();
        let alice_updated_comm = alice_updated.commit(account_comm_key.clone()).unwrap();

        let mut alice_builder =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account.clone(),
                alice_updated.clone(),
                alice_updated_comm,
                nonce,
            );
        alice_builder.add_irreversible_send(
            alice_to_bob_amount,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
        );
        alice_builder.add_irreversible_receive(
            carol_to_alice_amount,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
        );

        let start = Instant::now();
        let (alice_proof, alice_nullifier) = alice_builder
            .finalize(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time = start.elapsed();

        // Verify Alice's proof
        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_irreversible_send(leg_enc_1.clone());
        alice_verifier.add_irreversible_receive(leg_enc_2.clone());

        let start = Instant::now();
        alice_verifier
            .verify(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time = start.elapsed();
        let proof_size = alice_proof.compressed_size();
        println!(
            "Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time, verification_time, proof_size
        );
    }

    #[test]
    fn test_combined_multi_asset_proofs() {
        use ark_serialize::CanonicalSerialize;
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 14;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS>(b"test");

        // Setup keys for Alice and Bob
        let (((sk_alice, pk_alice), (_, pk_alice_e)), ((_, pk_bob), (_, pk_bob_e)), _) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id_1 = 1u32;
        let asset_id_2 = 2u32;
        let amount_1 = 100u64; // Alice sends to Bob in asset 1
        let amount_2 = 150u64; // Bob sends to Alice in asset 1
        let amount_3 = 200u64; // Alice sends to Bob in asset 2
        let amount_4 = 250u64; // Bob sends to Alice in asset 2

        // Create legs for asset 1
        let leg_1_asset1 = Leg::new(
            pk_alice.0,
            pk_bob.0,
            vec![(true, pk_auditor_e.0)],
            amount_1,
            asset_id_1,
        )
        .unwrap();
        let (leg_enc_1_asset1, leg_enc_rand_1_asset1) = leg_1_asset1
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_bob_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_2_asset1 = Leg::new(
            pk_bob.0,
            pk_alice.0,
            vec![(true, pk_auditor_e.0)],
            amount_2,
            asset_id_1,
        )
        .unwrap();
        let (leg_enc_2_asset1, leg_enc_rand_2_asset1) = leg_2_asset1
            .encrypt::<_, Blake2b512>(&mut rng, pk_bob_e.0, pk_alice_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create legs for asset 2
        let leg_1_asset2 = Leg::new(
            pk_alice.0,
            pk_bob.0,
            vec![(true, pk_auditor_e.0)],
            amount_3,
            asset_id_2,
        )
        .unwrap();
        let (leg_enc_1_asset2, leg_enc_rand_1_asset2) = leg_1_asset2
            .encrypt::<_, Blake2b512>(&mut rng, pk_alice_e.0, pk_bob_e.0, enc_key_gen, enc_gen)
            .unwrap();

        let leg_2_asset2 = Leg::new(
            pk_bob.0,
            pk_alice.0,
            vec![(true, pk_auditor_e.0)],
            amount_4,
            asset_id_2,
        )
        .unwrap();
        let (leg_enc_2_asset2, leg_enc_rand_2_asset2) = leg_2_asset2
            .encrypt::<_, Blake2b512>(&mut rng, pk_bob_e.0, pk_alice_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create Alice's accounts for both assets
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account_asset1, _, _) =
            new_account(&mut rng, asset_id_1, sk_alice.clone(), alice_id);
        alice_account_asset1.balance = 1000;

        let (mut alice_account_asset2, _, _) =
            new_account(&mut rng, asset_id_2, sk_alice, alice_id);
        alice_account_asset2.balance = 2000;

        // Commit both Alice accounts and create a single account tree with both
        let alice_comm_asset1 = alice_account_asset1
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_comm_asset2 = alice_account_asset2
            .commit(account_comm_key.clone())
            .unwrap();

        let account_comms = vec![alice_comm_asset1.0, alice_comm_asset2.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(4),
        );
        let account_tree_root = account_tree.root_node();

        // Get paths for both Alice accounts (asset1 at index 0, asset2 at index 1)
        let alice_path_asset1 = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let alice_path_asset2 = account_tree.get_path_to_leaf_for_proof(1, 0).unwrap();

        let nonce_alice_1 = b"alice_asset1";
        let nonce_alice_2 = b"alice_asset2";

        // Alice's updated states - each proof does send.
        let mut builder1 = AccountStateBuilder::init(alice_account_asset1.clone());
        builder1.update_for_send(amount_1).unwrap();
        builder1.update_for_receive();
        let alice_updated_asset1 = builder1.finalize();
        let alice_updated_comm_asset1 = alice_updated_asset1
            .commit(account_comm_key.clone())
            .unwrap();

        let mut builder2 = AccountStateBuilder::init(alice_account_asset2.clone());
        builder2.update_for_send(amount_3).unwrap();
        builder2.update_for_receive();
        let alice_updated_asset2 = builder2.finalize();
        let alice_updated_comm_asset2 = alice_updated_asset2
            .commit(account_comm_key.clone())
            .unwrap();

        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        // Alice creates builders for both assets using the single account tree
        let mut alice_builder_asset1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_asset1.clone(),
                alice_updated_asset1.clone(),
                alice_updated_comm_asset1,
                nonce_alice_1,
            );
        alice_builder_asset1.add_send_affirmation(
            amount_1,
            leg_enc_1_asset1.clone(),
            leg_enc_rand_1_asset1.clone(),
        );
        alice_builder_asset1
            .add_receive_affirmation(leg_enc_2_asset1.clone(), leg_enc_rand_2_asset1.clone());

        let mut alice_builder_asset2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_asset2.clone(),
                alice_updated_asset2.clone(),
                alice_updated_comm_asset2,
                nonce_alice_2,
            );
        alice_builder_asset2.add_send_affirmation(
            amount_3,
            leg_enc_1_asset2.clone(),
            leg_enc_rand_1_asset2.clone(),
        );
        alice_builder_asset2
            .add_receive_affirmation(leg_enc_2_asset2.clone(), leg_enc_rand_2_asset2.clone());

        let start = Instant::now();

        let (alice_proof_asset1, alice_nullifier_1) = alice_builder_asset1
            .finalize_with_given_prover(
                &mut rng,
                alice_path_asset1.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )
            .unwrap();

        let (alice_proof_asset2, alice_nullifier_2) = alice_builder_asset2
            .finalize_with_given_prover(
                &mut rng,
                alice_path_asset2.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )
            .unwrap();

        let (even_bp, odd_bp) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params, &mut rng).unwrap();

        let proving_time = start.elapsed();

        // Verification
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        let start = Instant::now();

        let mut alice_verifier_1 = AccountStateTransitionProofVerifier::init(
            alice_updated_comm_asset1,
            alice_nullifier_1,
            nonce_alice_1,
        );
        alice_verifier_1.add_send_affirmation(leg_enc_1_asset1.clone());
        alice_verifier_1.add_receive_affirmation(leg_enc_2_asset1.clone());

        alice_verifier_1
            .enforce_constraints_and_verify_only_sigma_protocols(
                &alice_proof_asset1,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                None,
            )
            .unwrap();

        let mut alice_verifier_2 = AccountStateTransitionProofVerifier::init(
            alice_updated_comm_asset2,
            alice_nullifier_2,
            nonce_alice_2,
        );
        alice_verifier_2.add_send_affirmation(leg_enc_1_asset2.clone());
        alice_verifier_2.add_receive_affirmation(leg_enc_2_asset2.clone());

        alice_verifier_2
            .enforce_constraints_and_verify_only_sigma_protocols(
                &alice_proof_asset2,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_verifier,
                &mut odd_verifier,
                None,
            )
            .unwrap();

        // Verify the single combined R1CS proof
        verify_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();

        let verification_time = start.elapsed();

        let total_proof_size = alice_proof_asset1.compressed_size()
            + alice_proof_asset2.compressed_size()
            + even_bp.compressed_size()
            + odd_bp.compressed_size();

        println!(
            "Proving time = {:?}, verification time = {:?}, total size = {} bytes",
            proving_time, verification_time, total_proof_size
        );
    }
}
