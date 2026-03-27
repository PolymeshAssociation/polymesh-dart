use crate::account::common::{
    CommonStateChangeProof, CommonStateChangeProver, StateChangeVerifier,
};
use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, BalanceChangeConfig,
    BalanceChangeProof, BalanceChangeProver, LegProverConfig, LegVerifierConfig,
};
use crate::leg::AmountCiphertext;
use crate::leg::LegEncryption;
use crate::leg::PartyEphemeralPublicKey;
use crate::util::{
    BPProof, get_verification_tuples_with_rng, handle_verification_tuples, prove_with_rng,
};
use crate::{TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL, error::Error, error::Result};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::marker::PhantomData;
use ark_std::{format, string::ToString, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use curve_tree_relations::curve_tree::Root;
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance};
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
    pub(crate) legs: Vec<LegProverConfig<G0>>,
    pub(crate) balance_changes: Vec<BalanceChangeConfig<G0>>,
    pub(crate) net_counter_change: i32,
    pub(crate) account: AccountState<Affine<G0>>,
    pub(crate) updated_account: AccountState<Affine<G0>>,
    pub(crate) updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub(crate) nonce: Vec<u8>,
    marker: PhantomData<G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
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

    pub fn add_send_affirmation(&mut self, amount: Balance, leg_enc: LegEncryption<Affine<G0>>) {
        let ct_amount = leg_enc.ct_amount();
        let eph_pk = leg_enc.eph_pk_s.clone();
        let eph_pk_amount = eph_pk.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
            has_balance_changed: true,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            eph_pk_amount,
            has_balance_decreased: true,
        });

        self.net_counter_change += 1;
    }

    pub fn add_receive_affirmation(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        let eph_pk_r = leg_enc.eph_pk_r.clone();
        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r),
            has_balance_changed: false,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.net_counter_change += 1;
    }

    pub fn add_claim_received(&mut self, amount: Balance, leg_enc: LegEncryption<Affine<G0>>) {
        let ct_amount = leg_enc.ct_amount();
        let eph_pk = leg_enc.eph_pk_r.clone();
        let eph_pk_amount = eph_pk.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk),
            has_balance_changed: true,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            eph_pk_amount,
            has_balance_decreased: false,
        });

        self.net_counter_change -= 1;
    }

    pub fn add_sender_counter_update(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        let eph_pk_s = leg_enc.eph_pk_s.clone();
        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s),
            has_balance_changed: false,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.net_counter_change -= 1;
    }

    pub fn add_sender_reverse(&mut self, amount: Balance, leg_enc: LegEncryption<Affine<G0>>) {
        let ct_amount = leg_enc.ct_amount();
        let eph_pk = leg_enc.eph_pk_s.clone();
        let eph_pk_amount = eph_pk.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
            has_balance_changed: true,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            eph_pk_amount,
            has_balance_decreased: false,
        });

        self.net_counter_change -= 1;
    }

    pub fn add_receiver_reverse(&mut self, leg_enc: LegEncryption<Affine<G0>>) {
        let eph_pk_r = leg_enc.eph_pk_r.clone();
        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r),
            has_balance_changed: false,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.net_counter_change -= 1;
    }

    pub fn add_irreversible_send(&mut self, amount: Balance, leg_enc: LegEncryption<Affine<G0>>) {
        let ct_amount = leg_enc.ct_amount();
        let eph_pk = leg_enc.eph_pk_s.clone();
        let eph_pk_amount = eph_pk.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk),
            has_balance_changed: true,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            eph_pk_amount,
            has_balance_decreased: true,
        });
    }

    pub fn add_irreversible_receive(
        &mut self,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
    ) {
        let ct_amount = leg_enc.ct_amount();
        let eph_pk = leg_enc.eph_pk_r.clone();
        let eph_pk_amount = eph_pk.2;

        self.legs.push(LegProverConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk),
            has_balance_changed: true,
            asset_id: leg_enc
                .is_asset_id_revealed()
                .then(|| self.account.asset_id),
        });

        self.balance_changes.push(BalanceChangeConfig {
            amount,
            ct_amount,
            eph_pk_amount,
            has_balance_decreased: false,
        });
    }

    pub fn finalize<
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
    ) -> Result<(AccountStateTransitionProof<L, F0, F1, G0, G1>, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens(),
            even_transcript,
        );
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.pc_gens(),
            odd_transcript,
        );

        let (mut proof, nullifier) = self
            .finalize_with_given_prover::<_, Parameters0, Parameters1>(
                rng,
                leaf_path,
                root,
                account_tree_params,
                account_comm_key,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )?;

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;

        proof.common_proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((proof, nullifier))
    }

    pub fn finalize_with_given_prover<
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
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(AccountStateTransitionProof<L, F0, F1, G0, G1>, Affine<G0>)> {
        self.pre_finalize_checks()?;

        let common_prover =
            CommonStateChangeProver::init_with_given_prover::<_, Parameters0, Parameters1>(
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
                enc_gen,
                even_prover,
                odd_prover,
            )?;

        self.generate_proof_given_common_prover(
            rng,
            common_prover,
            account_tree_params,
            enc_gen,
            even_prover,
        )
    }

    /// Creates a proof when the account leaf has already been re-randomized externally.
    /// This is useful for batched proving when proving multiple account paths at once.
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
            enc_gen,
            even_prover,
        )?;

        self.generate_proof_given_common_prover(
            rng,
            common_prover,
            account_tree_params,
            enc_gen,
            even_prover,
        )
    }

    fn generate_proof_given_common_prover<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        rng: &mut R,
        common_prover: CommonStateChangeProver<'a, L, F0, F1, G0, G1>,
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
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
                common_prover.sk_enc_inv_blinding,
                even_prover,
                &account_tree_params.even_parameters.pc_gens(),
                &account_tree_params.even_parameters.bp_gens(),
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

    pub(crate) fn pre_finalize_checks(&self) -> Result<()> {
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
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub(crate) legs: Vec<LegVerifierConfig<G0>>,
    pub(crate) net_counter_change: i32,
    pub(crate) updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub(crate) nullifier: Affine<G0>,
    pub(crate) nonce: Vec<u8>,
    marker: PhantomData<G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
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

    pub fn add_send_affirmation(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_s = leg_enc.eph_pk_s.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s),
            has_balance_decreased: Some(true),
            has_counter_decreased: Some(false),
            asset_id,
        });
        self.net_counter_change += 1;
    }

    pub fn add_receive_affirmation(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_r = leg_enc.eph_pk_r.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r),
            has_balance_decreased: None,
            has_counter_decreased: Some(false),
            asset_id,
        });
        self.net_counter_change += 1;
    }

    pub fn add_claim_received(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_r = leg_enc.eph_pk_r.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r),
            has_balance_decreased: Some(false),
            has_counter_decreased: Some(true),
            asset_id,
        });
        self.net_counter_change -= 1;
    }

    pub fn add_sender_counter_update(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_s = leg_enc.eph_pk_s.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s),
            has_balance_decreased: None,
            has_counter_decreased: Some(true),
            asset_id,
        });
        self.net_counter_change -= 1;
    }

    pub fn add_sender_reverse(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_s = leg_enc.eph_pk_s.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s),
            has_balance_decreased: Some(false),
            has_counter_decreased: Some(true),
            asset_id,
        });
        self.net_counter_change -= 1;
    }

    pub fn add_receiver_reverse(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_r = leg_enc.eph_pk_r.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r),
            has_balance_decreased: None,
            has_counter_decreased: Some(true),
            asset_id,
        });
        self.net_counter_change -= 1;
    }

    pub fn add_irreversible_send(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_s = leg_enc.eph_pk_s.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Sender(eph_pk_s),
            has_balance_decreased: Some(true),
            has_counter_decreased: None,
            asset_id,
        });
    }

    pub fn add_irreversible_receive(
        &mut self,
        leg_enc: LegEncryption<Affine<G0>>,
        asset_id: Option<AssetId>,
    ) {
        let eph_pk_r = leg_enc.eph_pk_r.clone();
        self.legs.push(LegVerifierConfig {
            encryption: leg_enc.core.clone(),
            party_eph_pk: PartyEphemeralPublicKey::Receiver(eph_pk_r),
            has_balance_decreased: Some(false),
            has_counter_decreased: None,
            asset_id,
        });
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>
{
    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        rng: &mut R,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
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

        let (even_tuple, odd_tuple) = self
            .verify_and_return_tuples::<_, Parameters0, Parameters1>(
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

    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        self.pre_verify_checks(proof)?;

        let mut verifier = StateChangeVerifier::init::<Parameters0, Parameters1>(
            &proof.common_proof,
            self.legs.clone(),
            root,
            self.updated_account_commitment,
            self.nullifier,
            &self.nonce,
            account_tree_params,
            &account_comm_key,
            enc_gen,
        )?;

        let mut even_verifier = verifier.even_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError(
                "even_verifier is missing or already consumed; use init() or init_with_given_verifier*"
                    .to_string(),
            )
        })?;
        let odd_verifier = verifier.odd_verifier.take().ok_or_else(|| {
            Error::ProofVerificationError(
                "odd_verifier is missing or already consumed; use init() or init_with_given_verifier*"
                    .to_string(),
            )
        })?;

        self.verify_sigma_protocols_given_state_change_verifier(
            proof,
            verifier,
            account_tree_params,
            account_comm_key,
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

    pub fn enforce_constraints_and_verify_only_sigma_protocols<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
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
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        self.verify_sigma_protocols_given_state_change_verifier(
            proof,
            verifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            even_verifier,
            rmc,
        )
    }

    /// Verifies the proof when the account leaf has already been re-randomized externally.
    /// This is useful for batched verification when verifying multiple account paths at once.
    /// `rerandomized_leaf` - The re-randomized leaf obtained from external batched curve tree operations.
    pub fn enforce_constraints_and_verify_only_sigma_protocols_with_rerandomized_leaf<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        rerandomized_leaf: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
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
            enc_gen,
            even_verifier,
        )?;

        self.verify_sigma_protocols_given_state_change_verifier(
            proof,
            verifier,
            account_tree_params,
            account_comm_key,
            enc_gen,
            even_verifier,
            rmc,
        )
    }

    fn verify_sigma_protocols_given_state_change_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        proof: &AccountStateTransitionProof<L, F0, F1, G0, G1>,
        mut verifier: StateChangeVerifier<L, F0, F1, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        if let Some(balance_proof) = &proof.balance_proof {
            // Filter legs and corresponding prover_is_sender entries together
            let ct_amounts: Vec<AmountCiphertext<Affine<G0>>> = self
                .legs
                .iter()
                .zip(verifier.prover_is_sender.iter())
                .filter(|(l, _)| l.has_balance_decreased.is_some())
                .map(|(l, _)| {
                    AmountCiphertext(l.encryption.ct_amount, l.party_eph_pk.eph_pk_amount())
                })
                .collect();

            verifier.init_balance_change_verification_with_given_verifier(
                balance_proof,
                &ct_amounts,
                enc_gen,
                even_verifier,
            )?;
        }

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let ct_amounts: Vec<AmountCiphertext<Affine<G0>>> = self
            .legs
            .iter()
            .map(|l| AmountCiphertext(l.encryption.ct_amount, l.party_eph_pk.eph_pk_amount()))
            .collect();

        verifier.verify_sigma_protocols(
            &proof.common_proof,
            proof.balance_proof.as_ref(),
            &challenge,
            ct_amounts,
            self.updated_account_commitment,
            self.nullifier,
            account_tree_params,
            &account_comm_key,
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
    use crate::account::tests::{get_tree_with_account_comm, setup_gens_new};
    use crate::account_registration::tests::new_account;
    use crate::leg::tests::setup_keys;
    use crate::leg::{Leg, LegEncConfig};
    use crate::util::{prove_with_rng, verify_rmc, verify_with_rng};
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use ark_std::UniformRand;
    use bulletproofs::r1cs::{Prover, Verifier};
    use curve_tree_relations::curve_tree::CurveTree;
    use rand::thread_rng;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasFr = ark_pallas::Fr;
    type VestaFr = ark_vesta::Fr;

    const TXN_EVEN_LABEL: &'static [u8] = b"PolymeshTransactionEven";
    const TXN_ODD_LABEL: &'static [u8] = b"PolymeshTransactionOdd";

    #[test]
    fn test_multi_leg_two_senders_one_receiver() {
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let tree_height = 6;

        // Setup keys for Alice, Bob, Carol, and auditor
        let ((_, (_, pk_alice_e)), (_, (_, pk_bob_e)), ((sk_carol, _), (sk_carol_e, pk_carol_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_send_amount = 100u64;
        let bob_send_amount = 200u64;

        let mut test_with_config = |reveal_asset_id: bool| {
            let conf = LegEncConfig {
                parties_see_each_other: true,
                reveal_asset_id,
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
            let (mut carol_account, _, _, _) = new_account(
                &mut rng,
                asset_id,
                sk_carol.clone(),
                sk_carol_e.clone(),
                carol_id,
            );
            carol_account.balance = 500;

            let account_tree = get_tree_with_account_comm::<L, _>(
                &carol_account,
                account_comm_key.clone(),
                &account_tree_params,
                tree_height,
            )
            .unwrap();

            println!("With L={L}, height={tree_height}, reveal_asset_id={reveal_asset_id}");

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
            let mut carol_builder_1 = AccountStateTransitionProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::init(
                carol_account.clone(),
                carol_receives.clone(),
                carol_receives_comm,
                nonce_1,
            );
            carol_builder_1.add_receive_affirmation(leg_enc_1.clone());
            carol_builder_1.add_receive_affirmation(leg_enc_2.clone());

            let start = Instant::now();
            let (carol_proof_1, carol_nullifier_1) = carol_builder_1
                .finalize::<_, PallasParams, VestaParams>(
                    &mut rng,
                    carol_leaf_path.clone(),
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
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
            carol_verifier_1
                .add_receive_affirmation(leg_enc_1.clone(), reveal_asset_id.then_some(asset_id));
            carol_verifier_1
                .add_receive_affirmation(leg_enc_2.clone(), reveal_asset_id.then_some(asset_id));

            let start = Instant::now();
            carol_verifier_1
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    &carol_proof_1,
                    &account_tree_root,
                    &account_tree_params,
                    account_comm_key.clone(),
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
            let account_tree_2 = get_tree_with_account_comm::<L, _>(
                &carol_receives,
                account_comm_key.clone(),
                &account_tree_params,
                6,
            )
            .unwrap();
            let carol_leaf_path_2 = account_tree_2.get_path_to_leaf_for_proof(0, 0).unwrap();
            let account_tree_root_2 = account_tree_2.root_node();

            // Carol creates multi-leg proof for claims
            let mut carol_builder_2 = AccountStateTransitionProofBuilder::<
                L,
                _,
                _,
                PallasParameters,
                VestaParameters,
            >::init(
                carol_receives.clone(),
                carol_final.clone(),
                carol_final_comm,
                nonce_2,
            );
            carol_builder_2.add_claim_received(alice_send_amount, leg_enc_1.clone());
            carol_builder_2.add_claim_received(bob_send_amount, leg_enc_2.clone());

            let start = Instant::now();
            let (carol_proof_2, carol_nullifier_2) = carol_builder_2
                .finalize::<_, PallasParams, VestaParams>(
                    &mut rng,
                    carol_leaf_path_2.clone(),
                    &account_tree_root_2,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_gen,
                )
                .unwrap();
            let proving_time_2 = start.elapsed();

            // Verify Carol's second proof
            let mut carol_verifier_2 = AccountStateTransitionProofVerifier::init(
                carol_final_comm,
                carol_nullifier_2,
                nonce_2,
            );
            carol_verifier_2
                .add_claim_received(leg_enc_1.clone(), reveal_asset_id.then_some(asset_id));
            carol_verifier_2
                .add_claim_received(leg_enc_2.clone(), reveal_asset_id.then_some(asset_id));

            let start = Instant::now();
            carol_verifier_2
                .verify::<_, PallasParams, VestaParams>(
                    &mut rng,
                    &carol_proof_2,
                    &account_tree_root_2,
                    &account_tree_params,
                    account_comm_key.clone(),
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
        };

        test_with_config(false);

        test_with_config(true);
    }

    #[test]
    fn test_multi_leg_sender_and_receiver() {
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();

        // Setup keys for Alice, Bob, Carol, and auditor
        let (
            ((sk_alice, _), (sk_alice_e, pk_alice_e)),
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
        let (mut alice_account, _, _, _) =
            new_account(&mut rng, asset_id, sk_alice, sk_alice_e, alice_id);
        alice_account.balance = 1000;

        // Alice sends and receives
        let mut builder = AccountStateBuilder::init(alice_account.clone());
        builder.update_for_send(alice_to_bob_amount).unwrap();
        builder.update_for_receive();
        let alice_updated = builder.finalize();
        let alice_updated_comm = alice_updated.commit(account_comm_key.clone()).unwrap();

        // Create account tree with both alice_account and alice_updated commitments.
        let alice_account_comm = alice_account.commit(account_comm_key.clone()).unwrap();
        let account_comms = vec![alice_account_comm.0, alice_updated_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(6),
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
        alice_builder.add_send_affirmation(alice_to_bob_amount, leg_enc_1.clone());
        alice_builder.add_receive_affirmation(leg_enc_2.clone());

        let start = Instant::now();
        let (alice_proof, alice_nullifier) = alice_builder
            .finalize::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();
        let proving_time_1 = start.elapsed();

        // Verify Alice's proof 1
        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_send_affirmation(leg_enc_1.clone(), None);
        alice_verifier.add_receive_affirmation(leg_enc_2.clone(), None);

        let start = Instant::now();
        alice_verifier
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
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
        alice_builder_2.add_claim_received(carol_to_alice_amount, leg_enc_2.clone());
        alice_builder_2.add_sender_counter_update(leg_enc_1.clone());

        let start = Instant::now();
        let (alice_proof_2, alice_nullifier_2) = alice_builder_2
            .finalize::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_leaf_path_2.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();
        let proving_time_2 = start.elapsed();

        // Verify Alice's proof 2
        let mut alice_verifier_2 =
            AccountStateTransitionProofVerifier::init(alice_final_comm, alice_nullifier_2, nonce_2);
        alice_verifier_2.add_claim_received(leg_enc_2.clone(), None);
        alice_verifier_2.add_sender_counter_update(leg_enc_1.clone(), None);

        let start = Instant::now();
        alice_verifier_2
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                &alice_proof_2,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
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
    }

    #[test]
    fn test_send_receive_and_reverse() {
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();

        // Setup keys for Alice, Bob, Carol, Dave, and auditor
        let (((sk_alice, _), (sk_alice_e, pk_alice_e)), (_, (_, pk_bob_e)), (_, (_, pk_carol_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, (_, pk_dave_e)) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen).0;
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_to_bob_amount = 100u64;
        let carol_to_alice_amount = 150u64;
        let alice_to_dave_amount = 50u64;
        let bob_to_alice_amount = 75u64;

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

        let leg_3 = Leg::new(
            pk_alice_e.0,
            pk_dave_e.0,
            alice_to_dave_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_3, _) = leg_3
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let leg_4 = Leg::new(
            pk_bob_e.0,
            pk_alice_e.0,
            bob_to_alice_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_4, _) = leg_4
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        // Create Alice's account
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account, _, _, _) =
            new_account(&mut rng, asset_id, sk_alice, sk_alice_e, alice_id);
        alice_account.balance = 1000;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &alice_account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let alice_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root = account_tree.root_node();
        let nonce = b"alice_nonce_4ops";

        // Alice does 4 operations in one proof
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
        alice_builder.add_send_affirmation(alice_to_bob_amount, leg_enc_1.clone());
        alice_builder.add_receive_affirmation(leg_enc_2.clone());
        alice_builder.add_sender_reverse(alice_to_dave_amount, leg_enc_3.clone());
        alice_builder.add_receiver_reverse(leg_enc_4.clone());

        let start = Instant::now();
        let (alice_proof, alice_nullifier) = alice_builder
            .finalize::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();
        let proving_time = start.elapsed();

        // Verify Alice's proof
        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_send_affirmation(leg_enc_1.clone(), None);
        alice_verifier.add_receive_affirmation(leg_enc_2.clone(), None);
        alice_verifier.add_sender_reverse(leg_enc_3.clone(), None);
        alice_verifier.add_receiver_reverse(leg_enc_4.clone(), None);

        let start = Instant::now();
        alice_verifier
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
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
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();

        // Setup keys for Alice, Bob, Carol, and auditor
        let (((sk_alice, _), (sk_alice_e, pk_alice_e)), (_, (_, pk_bob_e)), (_, (_, pk_carol_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_to_bob_amount = 200u64;
        let carol_to_alice_amount = 300u64;

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
        let (mut alice_account, _, _, _) =
            new_account(&mut rng, asset_id, sk_alice, sk_alice_e, alice_id);
        alice_account.balance = 1000;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &alice_account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let alice_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root = account_tree.root_node();
        let nonce = b"alice_nonce_irreversible";

        // Alice does 2 irreversible operations in one proof
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
        alice_builder.add_irreversible_send(alice_to_bob_amount, leg_enc_1.clone());
        alice_builder.add_irreversible_receive(carol_to_alice_amount, leg_enc_2.clone());

        let start = Instant::now();
        let (alice_proof, alice_nullifier) = alice_builder
            .finalize::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();
        let proving_time = start.elapsed();

        // Verify Alice's proof
        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_irreversible_send(leg_enc_1.clone(), None);
        alice_verifier.add_irreversible_receive(leg_enc_2.clone(), None);

        let start = Instant::now();
        alice_verifier
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
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
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 14;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();

        // Setup keys for Alice and Bob
        let (((sk_alice, _), (sk_alice_e, pk_alice_e)), (_, (_, pk_bob_e)), _) =
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
            pk_alice_e.0,
            pk_bob_e.0,
            amount_1,
            asset_id_1,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_1_asset1, _) = leg_1_asset1
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let leg_2_asset1 = Leg::new(
            pk_bob_e.0,
            pk_alice_e.0,
            amount_2,
            asset_id_1,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_2_asset1, _) = leg_2_asset1
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        // Create legs for asset 2
        let leg_1_asset2 = Leg::new(
            pk_alice_e.0,
            pk_bob_e.0,
            amount_3,
            asset_id_2,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_1_asset2, _) = leg_1_asset2
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        let leg_2_asset2 = Leg::new(
            pk_bob_e.0,
            pk_alice_e.0,
            amount_4,
            asset_id_2,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_2_asset2, _) = leg_2_asset2
            .encrypt(&mut rng, LegEncConfig::default(), enc_key_gen, enc_gen)
            .unwrap();

        // Create Alice's accounts for both assets
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account_asset1, _, _, _) = new_account(
            &mut rng,
            asset_id_1,
            sk_alice.clone(),
            sk_alice_e.clone(),
            alice_id,
        );
        alice_account_asset1.balance = 1000;

        let (mut alice_account_asset2, _, _, _) =
            new_account(&mut rng, asset_id_2, sk_alice, sk_alice_e, alice_id);
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
            Some(6),
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
            &account_tree_params.even_parameters.pc_gens(),
            even_transcript,
        );
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.pc_gens(),
            odd_transcript,
        );

        // Alice creates builders for both assets using the single account tree
        let mut alice_builder_asset1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_asset1.clone(),
                alice_updated_asset1.clone(),
                alice_updated_comm_asset1,
                nonce_alice_1,
            );
        alice_builder_asset1.add_send_affirmation(amount_1, leg_enc_1_asset1.clone());
        alice_builder_asset1.add_receive_affirmation(leg_enc_2_asset1.clone());

        let mut alice_builder_asset2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_asset2.clone(),
                alice_updated_asset2.clone(),
                alice_updated_comm_asset2,
                nonce_alice_2,
            );
        alice_builder_asset2.add_send_affirmation(amount_3, leg_enc_1_asset2.clone());
        alice_builder_asset2.add_receive_affirmation(leg_enc_2_asset2.clone());

        let start = Instant::now();

        let (alice_proof_asset1, alice_nullifier_1) = alice_builder_asset1
            .finalize_with_given_prover::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_path_asset1.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )
            .unwrap();

        let (alice_proof_asset2, alice_nullifier_2) = alice_builder_asset2
            .finalize_with_given_prover::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_path_asset2.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )
            .unwrap();

        let (even_bp, odd_bp) = prove_with_rng(
            even_prover,
            odd_prover,
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rng,
        )
        .unwrap();

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
        alice_verifier_1.add_send_affirmation(leg_enc_1_asset1.clone(), None);
        alice_verifier_1.add_receive_affirmation(leg_enc_2_asset1.clone(), None);

        alice_verifier_1
            .enforce_constraints_and_verify_only_sigma_protocols::<PallasParams, VestaParams>(
                &alice_proof_asset1,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
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
        alice_verifier_2.add_send_affirmation(leg_enc_1_asset2.clone(), None);
        alice_verifier_2.add_receive_affirmation(leg_enc_2_asset2.clone(), None);

        alice_verifier_2
            .enforce_constraints_and_verify_only_sigma_protocols::<PallasParams, VestaParams>(
                &alice_proof_asset2,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
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
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
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

    #[test]
    fn test_five_legs_mixed_revealed_asset_ids() {
        // Affirmation proof over 5 legs, in some prover is sender, in some it is receiver. Some of the legs reveal asset-id, some dont
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, enc_gen) = setup_gens_new::<NUM_GENS>(b"test");

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let (((sk_alice, _), (sk_alice_e, pk_alice_e)), (_, (_, pk_bob_e)), (_, (_, pk_carol_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let ((_, (_, pk_dave_e)), (_, (_, pk_eve_e)), (_, (_, pk_frank_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);
        let (_, _, (_, (_, pk_auditor_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1u32;
        let alice_to_bob_amount = 100u64;
        let alice_to_carol_amount = 150u64;
        let dave_to_alice_amount = 200u64;
        let eve_to_alice_amount = 250u64;
        let frank_to_alice_amount = 300u64;

        // Asset-id is revealed, Alice is sender
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

        // Asset-id is hidden, Alice is sender
        let leg_2 = Leg::new(
            pk_alice_e.0,
            pk_carol_e.0,
            alice_to_carol_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_2, _) = leg_2
            .encrypt(
                &mut rng,
                LegEncConfig {
                    parties_see_each_other: true,
                    reveal_asset_id: false,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        // Asset-id is revealed, Alice is receiver
        let leg_3 = Leg::new(
            pk_dave_e.0,
            pk_alice_e.0,
            dave_to_alice_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_3, _) = leg_3
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

        // Asset-id is hidden, Alice is receiver
        let leg_4 = Leg::new(
            pk_eve_e.0,
            pk_alice_e.0,
            eve_to_alice_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_4, _) = leg_4
            .encrypt(
                &mut rng,
                LegEncConfig {
                    parties_see_each_other: true,
                    reveal_asset_id: false,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        // Asset-id is hidden, Alice is receiver
        let leg_5 = Leg::new(
            pk_frank_e.0,
            pk_alice_e.0,
            frank_to_alice_amount,
            asset_id,
            vec![pk_auditor_e.0],
            vec![],
            vec![],
        )
        .unwrap();
        let (leg_enc_5, _) = leg_5
            .encrypt(
                &mut rng,
                LegEncConfig {
                    parties_see_each_other: true,
                    reveal_asset_id: false,
                },
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account, _, _, _) =
            new_account(&mut rng, asset_id, sk_alice, sk_alice_e, alice_id);
        alice_account.balance = 1000;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &alice_account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let alice_leaf_path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let account_tree_root = account_tree.root_node();
        let nonce = b"test-nonce";

        let mut builder = AccountStateBuilder::init(alice_account.clone());
        builder.update_for_send(alice_to_bob_amount).unwrap();
        builder.update_for_send(alice_to_carol_amount).unwrap();
        builder.update_for_receive();
        builder.update_for_receive();
        builder.update_for_receive();
        let alice_updated = builder.finalize();
        let alice_updated_comm = alice_updated.commit(account_comm_key.clone()).unwrap();

        let mut alice_builder =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account.clone(),
                alice_updated.clone(),
                alice_updated_comm,
                nonce,
            );
        alice_builder.add_send_affirmation(alice_to_bob_amount, leg_enc_1.clone());
        alice_builder.add_send_affirmation(alice_to_carol_amount, leg_enc_2.clone());
        alice_builder.add_receive_affirmation(leg_enc_3.clone());
        alice_builder.add_receive_affirmation(leg_enc_4.clone());
        alice_builder.add_receive_affirmation(leg_enc_5.clone());

        let start = Instant::now();
        let (alice_proof, alice_nullifier) = alice_builder
            .finalize::<_, PallasParams, VestaParams>(
                &mut rng,
                alice_leaf_path.clone(),
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
            )
            .unwrap();
        let proving_time = start.elapsed();

        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_send_affirmation(leg_enc_1.clone(), Some(asset_id));
        alice_verifier.add_send_affirmation(leg_enc_2.clone(), Some(asset_id));
        alice_verifier.add_receive_affirmation(leg_enc_3.clone(), Some(asset_id));
        alice_verifier.add_receive_affirmation(leg_enc_4.clone(), Some(asset_id));
        alice_verifier.add_receive_affirmation(leg_enc_5.clone(), Some(asset_id));

        let start = Instant::now();
        alice_verifier
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time = start.elapsed();

        let mut alice_verifier =
            AccountStateTransitionProofVerifier::init(alice_updated_comm, alice_nullifier, nonce);
        alice_verifier.add_send_affirmation(leg_enc_1.clone(), Some(asset_id));
        alice_verifier.add_send_affirmation(leg_enc_2.clone(), Some(asset_id));
        alice_verifier.add_receive_affirmation(leg_enc_3.clone(), Some(asset_id));
        alice_verifier.add_receive_affirmation(leg_enc_4.clone(), Some(asset_id));
        alice_verifier.add_receive_affirmation(leg_enc_5.clone(), Some(asset_id));

        let start = Instant::now();
        let mut rmc_1 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        alice_verifier
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                &alice_proof,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_gen,
                Some((&mut rmc_1, &mut rmc_0)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let verification_time_rmc = start.elapsed();

        let proof_size = alice_proof.compressed_size();
        println!(
            "5 legs (2 send [1 revealed, 1 hidden], 3 receive [1 revealed, 2 hidden]): Proving time = {:?}, verification time = {:?}, verification time (RMC) = {:?}, proof size = {} bytes",
            proving_time, verification_time, verification_time_rmc, proof_size
        );
    }
}
