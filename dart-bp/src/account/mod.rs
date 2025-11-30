pub mod common;
pub mod mint;
pub mod pob;
pub mod state;
pub mod state_transition;
pub mod state_transition_multi;
#[cfg(test)]
pub mod tests;

// use ark_crypto_primitives::crh::poseidon::TwoToOneCRH;
// use ark_crypto_primitives::crh::TwoToOneCRHScheme;
// use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use crate::leg::{LegEncryption, LegEncryptionRandomness};
use crate::util::{add_verification_tuples_to_rmc, BPProof};
use crate::util::{prove_with_rng, verify_given_verification_tuples};
use crate::{error::Result, Error, TXN_ODD_LABEL};
use crate::{TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::string::ToString;
use ark_std::vec::Vec;
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
pub use common::{
    BalanceChangeConfig, BalanceChangeProof, BalanceChangeProver, CommonStateChangeProof,
    CommonStateChangeProver, LegProverConfig, LegVerifierConfig, StateChangeVerifier,
};
pub use state_transition::{AccountStateTransitionProofBuilder, AccountStateTransitionProofVerifier, AccountStateTransitionProof};
pub use state_transition_multi::MultiAssetStateTransitionProof;
use curve_tree_relations::curve_tree::{Root, SelRerandParameters};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::Balance;
use rand_core::CryptoRngCore;
pub use state::{AccountCommitmentKeyTrait, AccountState, AccountStateBuilder, AccountStateCommitment};

// Consider using https://github.com/jymchng/sosecrets-rs for blindings as well as i know how many times the blinding is needed.

// NOTE: Commitments generated when committing Bulletproofs (using `commit` or `commit_vec`) are already added to the transcript

// Table for balance and counter changes for various txns

//       Txn type           |    Balance change    |   Counter change
//       ----------------------------------------------------------------
//          Affirm_s        |        -v            |      1         |
//          Affirm_r        |         0            |      1         |
//          Claim_r         |        +v            |     -1         |
//          CntUpd_s        |         0            |     -1         |
//          Reverse_s       |        +v            |     -1         |
//          Reverse_r       |         0            |     -1         |
//          Irr_Affirm_s    |        -v            |      0         |
//          Irr_Affirm_r    |        +v            |      0         |

/// This is the proof for "send" txn. Report section 5.1.7
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AffirmAsSenderTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
    pub balance_proof: BalanceChangeProof<F0, G0>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AffirmAsSenderTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            amount,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. old balance - new balance = amount.
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. new counter - old counter = 1
        // 6. initial rho is same in both old and new commitments
        // 7. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 8. randomness in new account commitment is square of randomness in old account commitment
        // 9. pk in leg has the sk in account commitment

        let ct_amount = leg_enc.ct_amount;

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc.clone(),
                randomness: leg_enc_rand,
                is_sender: true,
                has_balance_changed: true,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            vec![BalanceChangeConfig {
                amount,
                ct_amount,
                r_3: common_prover.r_3[0],
                has_balance_decreased: true,
            }],
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        let balance_proof = balance_change_prover.gen_proof(&challenge)?;

        Ok((
            Self {
                common_proof,
                balance_proof,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: Some(true),
                has_counter_decreased: Some(false),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: Some(true),
                has_counter_decreased: Some(false),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification_with_given_verifier(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
            even_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AffirmAsReceiverTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> AffirmAsReceiverTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. new counter - old counter = 1
        // 5. initial rho is same in both old and new commitments
        // 6. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 7. randomness in new account commitment is square of randomness in old account commitment
        // 8. pk in leg has the sk in account commitment

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc,
                randomness: leg_enc_rand,
                is_sender: false,
                has_balance_changed: false,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        Ok((Self { common_proof }, nullifier))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: None,
                has_counter_decreased: Some(false),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            None,
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: None,
                has_counter_decreased: Some(false),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            None,
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}

/// This is the proof for receiver claiming funds from a receive txn. Not present in report
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ClaimReceivedTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
    pub balance_proof: BalanceChangeProof<F0, G0>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> ClaimReceivedTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            amount,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. new balance - old balance = amount.
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. old counter - new counter = 1
        // 6. initial rho is same in both old and new commitments
        // 7. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 8. randomness in new account commitment is square of randomness in old account commitment
        // 9. pk in leg has the sk in account commitment

        let ct_amount = leg_enc.ct_amount;

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc,
                randomness: leg_enc_rand,
                is_sender: false,
                has_balance_changed: true,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            vec![BalanceChangeConfig {
                amount,
                ct_amount,
                r_3: common_prover.r_3[0],
                has_balance_decreased: false,
            }],
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        let balance_proof = balance_change_prover.gen_proof(&challenge)?;

        Ok((
            Self {
                common_proof,
                balance_proof,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: Some(false),
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: Some(false),
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification_with_given_verifier(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
            even_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}

/// This is the proof for sender sending counter update txn. Report calls it txn_cu
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderCounterUpdateTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SenderCounterUpdateTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. old counter - new counter = 1
        // 5. initial rho is same in both old and new commitments
        // 6. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 7. randomness in new account commitment is square of randomness in old account commitment
        // 8. pk in leg has the sk in account commitment

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc,
                randomness: leg_enc_rand,
                is_sender: true,
                has_balance_changed: false,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        Ok((Self { common_proof }, nullifier))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: None,
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            None,
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: None,
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            None,
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}

/// Used by sender to reverse his "send" txn and take back his funds
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderReverseTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
    pub balance_proof: BalanceChangeProof<F0, G0>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SenderReverseTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            amount,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. new balance - old balance = amount.
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. old counter - new counter = 1
        // 6. initial rho is same in both old and new commitments
        // 7. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 8. randomness in new account commitment is square of randomness in old account commitment
        // 9. pk in leg has the sk in account commitment

        let ct_amount = leg_enc.ct_amount;

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc,
                randomness: leg_enc_rand,
                is_sender: true,
                has_balance_changed: true,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            vec![BalanceChangeConfig {
                amount,
                ct_amount,
                r_3: common_prover.r_3[0],
                has_balance_decreased: false,
            }],
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        let balance_proof = balance_change_prover.gen_proof(&challenge)?;

        Ok((
            Self {
                common_proof,
                balance_proof,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: Some(false),
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: Some(false),
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification_with_given_verifier(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
            even_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}

/// This is the proof for receiver sending counter update txn.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiverCounterUpdateTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> ReceiverCounterUpdateTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. old counter - new counter = 1
        // 5. initial rho is same in both old and new commitments
        // 6. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 7. randomness in new account commitment is square of randomness in old account commitment
        // 8. pk in leg has the sk in account commitment

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc,
                randomness: leg_enc_rand,
                is_sender: false,
                has_balance_changed: false,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        Ok((Self { common_proof }, nullifier))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: None,
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            None,
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: None,
                has_counter_decreased: Some(true),
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            None,
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct IrreversibleAffirmAsSenderTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
    pub balance_proof: BalanceChangeProof<F0, G0>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> IrreversibleAffirmAsSenderTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            amount,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if account.counter != updated_account.counter {
            return Err(Error::ProofGenerationError(
                "counter mismatch between old and new account states".to_string(),
            ));
        }
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. old balance - new balance = amount.
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. new counter = old counter
        // 6. initial rho is same in both old and new commitments
        // 7. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 8. randomness in new account commitment is square of randomness in old account commitment
        // 9. pk in leg has the sk in account commitment

        let ct_amount = leg_enc.ct_amount;

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc,
                randomness: leg_enc_rand,
                is_sender: true,
                has_balance_changed: true,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            vec![BalanceChangeConfig {
                amount,
                ct_amount,
                r_3: common_prover.r_3[0],
                has_balance_decreased: true,
            }],
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        let balance_proof = balance_change_prover.gen_proof(&challenge)?;

        Ok((
            Self {
                common_proof,
                balance_proof,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: Some(true),
                has_counter_decreased: None,
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: true,
                has_balance_decreased: Some(true),
                has_counter_decreased: None,
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification_with_given_verifier(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
            even_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct IrreversibleAffirmAsReceiverTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub common_proof: CommonStateChangeProof<L, F0, F1, G0, G1>,
    pub balance_proof: BalanceChangeProof<F0, G0>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> IrreversibleAffirmAsReceiverTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let (mut proof, nullifier) = Self::new_with_given_prover(
            rng,
            amount,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if account.counter != updated_account.counter {
            return Err(Error::ProofGenerationError(
                "counter mismatch between old and new account states".to_string(),
            ));
        }
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. old balance - new balance = amount.
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. new counter = old counter
        // 6. initial rho is same in both old and new commitments
        // 7. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 8. randomness in new account commitment is square of randomness in old account commitment
        // 9. pk in leg has the sk in account commitment

        let ct_amount = leg_enc.ct_amount;

        let common_prover = CommonStateChangeProver::init_with_given_prover(
            rng,
            vec![LegProverConfig {
                encryption: leg_enc,
                randomness: leg_enc_rand,
                is_sender: false,
                has_balance_changed: true,
            }],
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            vec![BalanceChangeConfig {
                amount,
                ct_amount,
                r_3: common_prover.r_3[0],
                has_balance_decreased: false,
            }],
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof =
            common_prover.generate_sigma_responses(account, updated_account, &challenge)?;

        let balance_proof = balance_change_prover.gen_proof(&challenge)?;

        Ok((
            Self {
                common_proof,
                balance_proof,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
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
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
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

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: Some(false),
                has_counter_decreased: None,
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .as_mut()
            .unwrap()
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols_and_return_tuples(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let ct_amount = leg_enc.ct_amount;

        let mut verifier = StateChangeVerifier::init_with_given_verifier(
            &self.common_proof,
            vec![LegVerifierConfig {
                encryption: leg_enc.clone(),
                is_sender: false,
                has_balance_decreased: Some(false),
                has_counter_decreased: None,
            }],
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification_with_given_verifier(
            &self.balance_proof,
            &[ct_amount],
            enc_key_gen,
            enc_gen,
            even_verifier,
        )?;

        let challenge = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_sigma_protocols(
            &self.common_proof,
            Some(&self.balance_proof),
            &challenge,
            vec![leg_enc.clone()],
            updated_account_commitment,
            nullifier,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            rmc,
        )
    }
}
