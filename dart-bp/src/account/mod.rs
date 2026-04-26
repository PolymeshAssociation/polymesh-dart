pub mod common;
pub mod mint;
pub mod pob;
pub mod state;
pub mod state_transition;
pub mod state_transition_multi;
pub mod transparent;

pub mod state_transition_new;
#[cfg(test)]
pub mod tests;

pub use crate::leg::{AmountCiphertext, PartyEphemeralPublicKey};
pub use common::{CommonStateChangeProof, CommonStateChangeProver};

pub use state::{
    AccountCommitmentKeyTrait, AccountState, AccountStateBuilder, AccountStateCommitment,
};

pub use state_transition::AccountStateTransitionProof;

pub use state_transition_multi::MultiAssetStateTransitionProof;

use crate::auth_proofs::account::AuthProofAffirmation;
use crate::leg::{LegEncryptionCore, ReceiverEphemeralPublicKey, SenderEphemeralPublicKey};
use crate::util::{BPProof, handle_verification_tuples, prove_with_rng};
use crate::{Error, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL, error::Result};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{string::ToString, vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
pub use common::balance::BalanceChangeConfig;
pub use common::balance::BalanceChangeProof;
pub use common::balance::BalanceChangeProofPartial;
pub use common::balance::BalanceChangeProver;
pub use common::balance::BalanceChangeSplitProof;
use common::balance::BalanceSplitProver;
pub use common::balance::ensure_correct_balance_change;
pub use common::ensure_same_accounts;
pub use common::leg_link::LegProverConfig;
pub use common::leg_link::LegVerifierConfig;
pub use common::verifier::SplitStateChangeVerifier;
pub use common::verifier::StateChangeVerifier;
use common::{
    CommonAffirmationHostProof, CommonAffirmationSplitProof, CommonAffirmationSplitProtocol,
};
use curve_tree_relations::curve_tree::Root;
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::Balance;
use rand_core::CryptoRngCore;
pub use state_transition::AccountStateTransitionProofBuilder;
pub use state_transition::AccountStateTransitionProofVerifier;
pub use state_transition_new::AccountStateTransitionSplitProof;
pub use state_transition_new::AccountStateTransitionSplitProofBuilder;
pub use state_transition_new::AccountStateTransitionSplitProtocol;
pub use state_transition_new::MultiAssetStateTransitionHostProtocol;
pub use state_transition_new::MultiAssetStateTransitionSplitProof;

// For most protocols, only leaf level rmc is sufficient

/// Generates a TxnProof struct and its full `impl` block.
///
/// Two arms:
///   `has_balance: true`  — proof includes a `BalanceChangeProof` field.
///   `has_balance: false` — proof has only a `CommonStateChangeProof` field.
///
/// Key parameters:
///   `eph_pk_type`    — `SenderEphemeralPublicKey` or `ReceiverEphemeralPublicKey`
///   `eph_pk_variant` — `Sender` or `Receiver` (the `PartyEphemeralPublicKey` variant)
///   `verifier_has_counter_decreased` — forwarded to `LegVerifierConfig`
///   `check_counter_equality: yes | no` — if `yes`, `new_with_given_prover` validates
///       that the old and new account counters are equal (used by Irreversible variants).
///
/// Additional (for `has_balance: true`):
///   `prover_has_balance_decreased`   — forwarded to `BalanceChangeConfig`
///   `verifier_has_balance_decreased` — forwarded to `LegVerifierConfig`
macro_rules! impl_txn_proof {
    // generate the counter-equality check or nothing
    (@maybe_check_counter yes, $acc:ident, $new_acc:ident) => {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if $acc.counter != $new_acc.counter {
            return Err(Error::ProofGenerationError(
                "counter mismatch between old and new account states".to_string(),
            ));
        }
    };
    (@maybe_check_counter no, $acc:ident, $new_acc:ident) => {};

    // generate the `verify` method (identical for both balance variants)
    (@gen_verify $EphPkType:ident) => {
        pub fn verify<
            R: CryptoRngCore,
            Parameters0: DiscreteLogParameters,
            Parameters1: DiscreteLogParameters,
        >(
            &self,
            rng: &mut R,
            leg_enc: (
                LegEncryptionCore<Affine<G0>>,
                $EphPkType<Affine<G0>>,
            ),
            account_tree_root: &Root<L, 1, G0, G1>,
            updated_account_commitment: AccountStateCommitment<Affine<G0>>,
            nullifier: Affine<G0>,
            nonce: &[u8],
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
                    leg_enc,
                    account_tree_root,
                    updated_account_commitment,
                    nullifier,
                    nonce,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    rng,
                    rmc_0,
                )?;
            handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
        }
    };

    // generate the `new` method.
    // Pass `$amount` to include an `amount: Balance` parameter (for balance-change proofs).
    // Omit `$amount` for proofs without a balance change.
    (@gen_new $EphPkType:ident $(, $amount:ident)?) => {
        pub fn new<
            R: CryptoRngCore,
            Parameters0: DiscreteLogParameters,
            Parameters1: DiscreteLogParameters,
        >(
            rng: &mut R,
            $($amount: Balance,)?
            leg_enc: (
                LegEncryptionCore<Affine<G0>>,
                $EphPkType<Affine<G0>>,
            ),
            sk_aff: G0::ScalarField,
            sk_enc: G0::ScalarField,
            account: &AccountState<Affine<G0>>,
            updated_account: &AccountState<Affine<G0>>,
            updated_account_commitment: AccountStateCommitment<Affine<G0>>,
            leaf_path: CurveTreeWitnessPath<L, G0, G1>,
            account_tree_root: &Root<L, 1, G0, G1>,
            nonce: &[u8],
            account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
            account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
            enc_gen: Affine<G0>,
        ) -> Result<(Self, Affine<G0>)> {
            let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
            let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
            let mut even_prover = Prover::new(
                account_tree_params.even_parameters.pc_gens(),
                even_transcript,
            );
            let mut odd_prover =
                Prover::new(account_tree_params.odd_parameters.pc_gens(), odd_transcript);

            let (mut proof, nullifier) =
                Self::new_with_given_prover::<_, Parameters0, Parameters1>(
                    rng,
                    $($amount,)?
                    leg_enc,
                    sk_aff,
                    sk_enc,
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

            let (even_proof, odd_proof) = prove_with_rng(
                even_prover,
                odd_prover,
                &account_tree_params.even_parameters.bp_gens(),
                &account_tree_params.odd_parameters.bp_gens(),
                rng,
            )?;

            proof.common_proof.partial.r1cs_proof = Some(BPProof {
                even_proof,
                odd_proof,
            });

            Ok((proof, nullifier))
        }
    };

    // With balance change
    (
        $(#[$attr:meta])*
        $StructName:ident,
        eph_pk_type: $EphPkType:ident,
        eph_pk_variant: $EphPkVariant:ident,
        has_balance: true,
        prover_has_balance_decreased: $prover_bal_dec:expr,
        verifier_has_balance_decreased: $ver_bal_dec:expr,
        verifier_has_counter_decreased: $ver_ctr_dec:expr,
        check_counter_equality: $check:ident
    ) => {
        $(#[$attr])*
        #[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
        pub struct $StructName<
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
            G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > $StructName<L, F0, F1, G0, G1>
        {
            impl_txn_proof!(@gen_new $EphPkType, amount);

            pub fn new_with_given_prover<
                'a,
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                rng: &mut R,
                amount: Balance,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                sk_aff: G0::ScalarField,
                sk_enc: G0::ScalarField,
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
            ) -> Result<(Self, Affine<G0>)> {
                impl_txn_proof!(@maybe_check_counter $check, account, updated_account);
                let ct_amount = leg_enc.0.ct_amount;
                let (leg_enc_core, eph_pk) = leg_enc;
                let eph_pk_amount = eph_pk.r3;

                let common_prover =
                    CommonStateChangeProver::init_with_given_prover::<_, Parameters0, Parameters1>(
                        rng,
                        vec![LegProverConfig {
                            encryption: leg_enc_core,
                            party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(eph_pk),
                            has_balance_changed: true,
                        }],
                        sk_enc,
                        account,
                        updated_account,
                        updated_account_commitment,
                        leaf_path,
                        account_tree_root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        even_prover,
                        odd_prover,
                    )?;

                let balance_change_prover = BalanceChangeProver::init(
                    rng,
                    vec![BalanceChangeConfig {
                        amount,
                        ct_amount,
                        eph_pk_amount,
                        has_balance_decreased: $prover_bal_dec,
                    }],
                    sk_enc,
                    account,
                    updated_account,
                    common_prover.old_balance_blinding,
                    common_prover.new_balance_blinding,
                    common_prover.sk_enc_inv_blinding,
                    even_prover,
                    account_tree_params.even_parameters.pc_gens(),
                    account_tree_params.even_parameters.bp_gens(),
                    enc_gen,
                )?;

                let nullifier = common_prover.nullifier;

                let challenge = even_prover
                    .transcript()
                    .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

                let common_proof =
                    common_prover.generate_sigma_responses(sk_aff, sk_enc, account, updated_account, &challenge)?;

                let balance_proof = balance_change_prover.gen_proof(&challenge)?;

                Ok((
                    Self {
                        common_proof,
                        balance_proof,
                    },
                    nullifier,
                ))
            }

            impl_txn_proof!(@gen_verify $EphPkType);

            /// Verifies the proof except for final Bulletproof verification
            pub fn verify_and_return_tuples<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                account_tree_root: &Root<L, 1, G0, G1>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                rng: &mut R,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
                let ct_amount = leg_enc.0.ct_amount;
                let eph_pk_amount = leg_enc.1.r3;

                let mut verifier = StateChangeVerifier::init::<Parameters0, Parameters1>(
                    &self.common_proof,
                    vec![LegVerifierConfig {
                        encryption: leg_enc.0.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(leg_enc.1.clone()),
                        has_balance_decreased: $ver_bal_dec,
                        has_counter_decreased: $ver_ctr_dec,
                    }],
                    account_tree_root,
                    updated_account_commitment,
                    nullifier,
                    nonce,
                    account_tree_params,
                    &account_comm_key,
                    enc_gen,
                )?;

                verifier.init_balance_change_verification(
                    &self.balance_proof,
                    &[AmountCiphertext(ct_amount, eph_pk_amount)],
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
                    vec![AmountCiphertext(ct_amount, eph_pk_amount)],
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    rng,
                    rmc,
                )
            }

            pub fn enforce_constraints_and_verify_only_sigma_protocols<
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                account_tree_root: &Root<L, 1, G0, G1>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
                odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<()> {
                let ct_amount = leg_enc.0.ct_amount;
                let eph_pk_amount = leg_enc.1.r3;
                let (leg_enc_core, eph_pk) = leg_enc;

                let mut verifier = StateChangeVerifier::init_with_given_verifier(
                    &self.common_proof,
                    vec![LegVerifierConfig {
                        encryption: leg_enc_core,
                        party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(eph_pk),
                        has_balance_decreased: $ver_bal_dec,
                        has_counter_decreased: $ver_ctr_dec,
                    }],
                    account_tree_root,
                    updated_account_commitment,
                    nullifier,
                    nonce,
                    account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    even_verifier,
                    odd_verifier,
                )?;

                verifier.init_balance_change_verification_with_given_verifier(
                    &self.balance_proof,
                    &[AmountCiphertext(ct_amount, eph_pk_amount)],
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
                    vec![AmountCiphertext(ct_amount, eph_pk_amount)],
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    rmc,
                )
            }
        }
    };

    // Without balance change
    (
        $(#[$attr:meta])*
        $StructName:ident,
        eph_pk_type: $EphPkType:ident,
        eph_pk_variant: $EphPkVariant:ident,
        has_balance: false,
        verifier_has_counter_decreased: $ver_ctr_dec:expr,
        check_counter_equality: $check:ident
    ) => {
        $(#[$attr])*
        #[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
        pub struct $StructName<
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
            G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > $StructName<L, F0, F1, G0, G1>
        {
            impl_txn_proof!(@gen_new $EphPkType);

            pub fn new_with_given_prover<
                'a,
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                rng: &mut R,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                sk_aff: G0::ScalarField,
                sk_enc: G0::ScalarField,
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
            ) -> Result<(Self, Affine<G0>)> {
                impl_txn_proof!(@maybe_check_counter $check, account, updated_account);
                let (leg_enc_core, eph_pk) = leg_enc;

                let common_prover =
                    CommonStateChangeProver::init_with_given_prover::<_, Parameters0, Parameters1>(
                        rng,
                        vec![LegProverConfig {
                            encryption: leg_enc_core,
                            party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(eph_pk),
                            has_balance_changed: false,
                        }],
                        sk_enc,
                        account,
                        updated_account,
                        updated_account_commitment,
                        leaf_path,
                        account_tree_root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        even_prover,
                        odd_prover,
                    )?;

                let nullifier = common_prover.nullifier;

                let challenge = even_prover
                    .transcript()
                    .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

                let common_proof =
                    common_prover.generate_sigma_responses(sk_aff, sk_enc, account, updated_account, &challenge)?;

                Ok((Self { common_proof }, nullifier))
            }

            impl_txn_proof!(@gen_verify $EphPkType);

            /// Verifies the proof except for final Bulletproof verification
            pub fn verify_and_return_tuples<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                account_tree_root: &Root<L, 1, G0, G1>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                rng: &mut R,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
                let mut verifier = StateChangeVerifier::init::<Parameters0, Parameters1>(
                    &self.common_proof,
                    vec![LegVerifierConfig {
                        encryption: leg_enc.0.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(leg_enc.1.clone()),
                        has_balance_decreased: None,
                        has_counter_decreased: $ver_ctr_dec,
                    }],
                    account_tree_root,
                    updated_account_commitment,
                    nullifier,
                    nonce,
                    account_tree_params,
                    &account_comm_key,
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
                    vec![],
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    rng,
                    rmc,
                )
            }

            pub fn enforce_constraints_and_verify_only_sigma_protocols<
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                account_tree_root: &Root<L, 1, G0, G1>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
                odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<()> {
                let verifier = StateChangeVerifier::init_with_given_verifier(
                    &self.common_proof,
                    vec![LegVerifierConfig {
                        encryption: leg_enc.0.clone(),
                        party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(leg_enc.1.clone()),
                        has_balance_decreased: None,
                        has_counter_decreased: $ver_ctr_dec,
                    }],
                    account_tree_root,
                    updated_account_commitment,
                    nullifier,
                    nonce,
                    account_tree_params,
                    &account_comm_key,
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
                    vec![],
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    &account_comm_key,
                    enc_gen,
                    rmc,
                )
            }
        }
    };
}

/// Generates a split Protocol struct + Proof struct for the W2/W3 (host+auth) workflow.
///
/// Two arms:
///   `has_balance: true`  — protocol includes a `BalanceSplitProver`; proof includes a
///                          `BalanceChangeSplitProof`.
///   `has_balance: false` — no balance fields.
///
/// Key parameters (same semantics as `impl_txn_proof`):
///   `eph_pk_type`    — `SenderEphemeralPublicKey` or `ReceiverEphemeralPublicKey`
///   `eph_pk_variant` — `Sender` or `Receiver` (the `PartyEphemeralPublicKey` variant)
///   `verifier_has_counter_decreased` — forwarded to `LegVerifierConfig`
///   `check_counter_equality: yes | no`
///
/// Additional (for `has_balance: true`):
///   `prover_has_balance_decreased`   — forwarded to `BalanceChangeConfig`
///   `verifier_has_balance_decreased` — forwarded to `LegVerifierConfig`
macro_rules! impl_txn_split_proof {
    // Counter equality check (on AccountState)
    (@maybe_check_counter yes, $acc:ident, $new_acc:ident) => {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if $acc.counter != $new_acc.counter {
            return Err(Error::ProofGenerationError(
                "counter mismatch between old and new account states".to_string(),
            ));
        }
    };
    (@maybe_check_counter no, $acc:ident, $new_acc:ident) => {};

    // accessor methods shared by both arms
    (@gen_protocol_accessors) => {
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
    };

    // ── With balance change ─────────────────────────────────────────────
    (
        $(#[$proto_attr:meta])*
        $ProtocolName:ident,
        $(#[$proof_attr:meta])*
        $ProofName:ident,
        eph_pk_type: $EphPkType:ident,
        eph_pk_variant: $EphPkVariant:ident,
        has_balance: true,
        prover_has_balance_decreased: $prover_bal_dec:expr,
        verifier_has_balance_decreased: $ver_bal_dec:expr,
        verifier_has_counter_decreased: $ver_ctr_dec:expr,
        check_counter_equality: $check:ident
    ) => {
        $(#[$proto_attr])*
        pub struct $ProtocolName<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > {
            pub inner: CommonAffirmationSplitProtocol<L, F0, F1, G0, G1>,
            pub balance_prover: BalanceSplitProver<F0, G0>,
        }

        impl<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > $ProtocolName<L, F0, F1, G0, G1>
        {
            pub fn init<
                'a,
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                rng: &mut R,
                amount: Balance,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                account: &AccountState<Affine<G0>>,
                updated_account: &AccountState<Affine<G0>>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                leaf_path: CurveTreeWitnessPath<L, G0, G1>,
                account_tree_root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                k_amount: F0,
                k_asset_id: Option<F0>,
            ) -> Result<(
                Self,
                Prover<'a, MerlinTranscript, Affine<G0>>,
                Prover<'a, MerlinTranscript, Affine<G1>>,
                Affine<G0>,
            )> {
                impl_txn_split_proof!(@maybe_check_counter $check, account, updated_account);
                let ct_amount = leg_enc.0.ct_amount;
                let eph_pk_amount = leg_enc.1.r3;
                let (leg_enc_core, eph_pk) = leg_enc;

                let k_asset_ids: Vec<F0> = k_asset_id.into_iter().collect();

                let balance_changes = vec![BalanceChangeConfig {
                    amount,
                    ct_amount,
                    eph_pk_amount,
                    has_balance_decreased: $prover_bal_dec,
                }];

                let (inner, mut even_prover, odd_prover, nullifier) =
                    CommonAffirmationSplitProtocol::init::<_, Parameters0, Parameters1>(
                        rng,
                        vec![LegProverConfig {
                            encryption: leg_enc_core,
                            party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(eph_pk),
                            has_balance_changed: true,
                        }],
                        account,
                        updated_account,
                        updated_account_commitment,
                        leaf_path,
                        account_tree_root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        &k_asset_ids,
                    )?;

                let balance_prover = BalanceSplitProver::init(
                    rng,
                    &balance_changes,
                    account.balance,
                    updated_account.balance,
                    inner.old_balance_blinding(),
                    inner.new_balance_blinding(),
                    enc_gen,
                    &[k_amount],
                    &mut even_prover,
                    &account_tree_params.even_parameters.pc_gens(),
                    &account_tree_params.even_parameters.bp_gens(),
                )?;

                Ok((
                    Self {
                        inner,
                        balance_prover,
                    },
                    even_prover,
                    odd_prover,
                    nullifier,
                ))
            }

            impl_txn_split_proof!(@gen_protocol_accessors);

            /// Generate the host's proofs, consuming the protocol.
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
                BalanceChangeSplitProof<F0, G0>,
            )> {
                let host_data = self.inner.gen_proof::<_, Parameters0, Parameters1>(
                    challenge,
                    even_prover,
                    odd_prover,
                    account_tree_params,
                    rng,
                )?;
                let (balance_proof_partial, resp_ct_amount) = self.balance_prover.gen_proof(challenge)?;
                let balance = BalanceChangeSplitProof {
                    partial: balance_proof_partial,
                    resp_ct_amount,
                };
                Ok((host_data, balance))
            }

            /// `init` + challenge derivation + `gen_proof` in one call.
            /// Returns `(host_data, balance, rerandomized_leaf, auth_rerandomization, auth_rand_new_comm, nullifier)`.
            /// The caller still creates `auth_proof` and calls `assemble`.
            pub fn new<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                rng: &mut R,
                amount: Balance,
                leg_enc: (LegEncryptionCore<Affine<G0>>, $EphPkType<Affine<G0>>),
                account: &AccountState<Affine<G0>>,
                updated_account: &AccountState<Affine<G0>>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                leaf_path: CurveTreeWitnessPath<L, G0, G1>,
                account_tree_root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                k_amount: F0,
                k_asset_id: Option<F0>,
            ) -> Result<(
                CommonAffirmationHostProof<L, F0, F1, G0, G1>,
                BalanceChangeSplitProof<F0, G0>,
                Affine<G0>, // rerandomized_leaf
                F0,         // auth_rerandomization
                F0,         // auth_rand_new_comm
                Affine<G0>, // nullifier
            )> {
                let (protocol, mut even_prover, odd_prover, nullifier) =
                    Self::init::<_, Parameters0, Parameters1>(
                        rng,
                        amount,
                        leg_enc,
                        account,
                        updated_account,
                        updated_account_commitment,
                        leaf_path,
                        account_tree_root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        k_amount,
                        k_asset_id,
                    )?;
                let rerandomized_leaf = protocol.rerandomized_leaf();
                let auth_rerandomization = protocol.auth_rerandomization();
                let auth_rand_new_comm = protocol.auth_rand_new_comm();
                let challenge = even_prover
                    .transcript()
                    .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
                let (host_data, balance) = protocol.gen_proof::<_, Parameters0, Parameters1>(
                    &challenge,
                    even_prover,
                    odd_prover,
                    account_tree_params,
                    rng,
                )?;
                Ok((
                    host_data,
                    balance,
                    rerandomized_leaf,
                    auth_rerandomization,
                    auth_rand_new_comm,
                    nullifier,
                ))
            }
        }

        $(#[$proof_attr])*
        #[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
        pub struct $ProofName<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > {
            pub common: CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
            pub balance: BalanceChangeSplitProof<F0, G0>,
        }

        impl<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > $ProofName<L, F0, F1, G0, G1>
        {
            /// Assemble the final split proof from host data, balance data, and auth proof.
            pub fn assemble(
                host_data: CommonAffirmationHostProof<L, F0, F1, G0, G1>,
                balance: BalanceChangeSplitProof<F0, G0>,
                auth_proof: AuthProofAffirmation<Affine<G0>>,
            ) -> Self {
                Self {
                    common: CommonAffirmationSplitProof::assemble(host_data, auth_proof),
                    balance,
                }
            }

            /// Set up BP constraints and write all challenge contributions to transcript.
            /// Returns a `SplitStateChangeVerifier` whose transcript can be used to derive the challenge.
            pub fn challenge_contribution<
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                leg_enc: &LegEncryptionCore<Affine<G0>>,
                eph_pk: &$EphPkType<Affine<G0>>,
            ) -> Result<SplitStateChangeVerifier<L, F0, F1, G0, G1>> {
                let legs_with_conf = vec![LegVerifierConfig {
                    encryption: leg_enc.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(eph_pk.clone()),
                    has_balance_decreased: $ver_bal_dec,
                    has_counter_decreased: $ver_ctr_dec,
                }];

                let mut verifier = SplitStateChangeVerifier::init::<Parameters0, Parameters1>(
                    &self.common,
                    legs_with_conf,
                    updated_account_commitment,
                    nullifier,
                    root,
                    nonce,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                )?;

                let B_blinding = account_tree_params.even_parameters.pc_gens().B_blinding;
                verifier.init_balance_change_verification(
                    &self.common,
                    &self.balance,
                    enc_gen,
                    B_blinding,
                )?;

                Ok(verifier)
            }

            /// Verify all sigma protocols using the externally-derived challenge.
            pub fn verify_and_return_tuples<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                verifier: SplitStateChangeVerifier<L, F0, F1, G0, G1>,
                challenge: &F0,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                rng: &mut R,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
                verifier.verify_sigma_protocols_and_return_tuples(
                    &self.common,
                    Some(&self.balance),
                    challenge,
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    rng,
                    rmc,
                )
            }

            /// `challenge_contribution` + challenge derivation + `verify_and_return_tuples`.
            /// Returns `(even_tuple, odd_tuple)`.
            /// Note: `auth_proof` verification is the caller's responsibility (independent Ledger step).
            pub fn verify_with_tuples<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                leg_enc: &LegEncryptionCore<Affine<G0>>,
                eph_pk: &$EphPkType<Affine<G0>>,
                rng: &mut R,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
                let mut verifier = self.challenge_contribution::<Parameters0, Parameters1>(
                    updated_account_commitment,
                    nullifier,
                    root,
                    nonce,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    leg_enc,
                    eph_pk,
                )?;
                let challenge = verifier
                    .even_verifier
                    .as_mut()
                    .unwrap()
                    .transcript()
                    .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
                self.verify_and_return_tuples::<_, Parameters0, Parameters1>(
                    verifier,
                    &challenge,
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    rng,
                    rmc,
                )
            }

            /// Verify only sigma protocols using the externally-derived challenge.
            /// Does not perform R1CS verification; use when batching R1CS separately.
            pub fn verify_sigma_protocols<
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                verifier: SplitStateChangeVerifier<L, F0, F1, G0, G1>,
                challenge: &F0,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<()> {
                verifier.verify_sigma_protocols(
                    &self.common,
                    Some(&self.balance),
                    challenge,
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    rmc,
                )
            }

            pub fn verify<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                leg_enc: &LegEncryptionCore<Affine<G0>>,
                eph_pk: &$EphPkType<Affine<G0>>,
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
                let (even_tuple, odd_tuple) =
                    self.verify_with_tuples::<_, Parameters0, Parameters1>(
                        updated_account_commitment,
                        nullifier,
                        root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        leg_enc,
                        eph_pk,
                        rng,
                        rmc_0,
                    )?;
                handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
            }
        }
    };

    // ── Without balance change ──────────────────────────────────────────
    (
        $(#[$proto_attr:meta])*
        $ProtocolName:ident,
        $(#[$proof_attr:meta])*
        $ProofName:ident,
        eph_pk_type: $EphPkType:ident,
        eph_pk_variant: $EphPkVariant:ident,
        has_balance: false,
        verifier_has_counter_decreased: $ver_ctr_dec:expr,
        check_counter_equality: $check:ident
    ) => {
        $(#[$proto_attr])*
        pub struct $ProtocolName<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > {
            pub inner: CommonAffirmationSplitProtocol<L, F0, F1, G0, G1>,
        }

        impl<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > $ProtocolName<L, F0, F1, G0, G1>
        {
            pub fn init<
                'a,
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                rng: &mut R,
                leg_enc: (
                    LegEncryptionCore<Affine<G0>>,
                    $EphPkType<Affine<G0>>,
                ),
                account: &AccountState<Affine<G0>>,
                updated_account: &AccountState<Affine<G0>>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                leaf_path: CurveTreeWitnessPath<L, G0, G1>,
                account_tree_root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                k_asset_id: Option<F0>,
            ) -> Result<(
                Self,
                Prover<'a, MerlinTranscript, Affine<G0>>,
                Prover<'a, MerlinTranscript, Affine<G1>>,
                Affine<G0>,
            )> {
                impl_txn_split_proof!(@maybe_check_counter $check, account, updated_account);
                let (leg_enc_core, eph_pk) = leg_enc;

                let k_asset_ids: Vec<F0> = k_asset_id.into_iter().collect();

                let (inner, even_prover, odd_prover, nullifier) =
                    CommonAffirmationSplitProtocol::init::<_, Parameters0, Parameters1>(
                        rng,
                        vec![LegProverConfig {
                            encryption: leg_enc_core,
                            party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(eph_pk),
                            has_balance_changed: false,
                        }],
                        account,
                        updated_account,
                        updated_account_commitment,
                        leaf_path,
                        account_tree_root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        &k_asset_ids,
                    )?;

                Ok((Self { inner }, even_prover, odd_prover, nullifier))
            }

            impl_txn_split_proof!(@gen_protocol_accessors);

            /// Generate the host's proofs, consuming the protocol.
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
            ) -> Result<CommonAffirmationHostProof<L, F0, F1, G0, G1>> {
                self.inner.gen_proof::<_, Parameters0, Parameters1>(
                    challenge,
                    even_prover,
                    odd_prover,
                    account_tree_params,
                    rng,
                )
            }

            /// `init` + challenge derivation + `gen_proof` in one call.
            /// Returns `(host_data, rerandomized_leaf, auth_rerandomization, auth_rand_new_comm, nullifier)`.
            /// The caller still creates `auth_proof` and calls `assemble`.
            pub fn new<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                rng: &mut R,
                leg_enc: (LegEncryptionCore<Affine<G0>>, $EphPkType<Affine<G0>>),
                account: &AccountState<Affine<G0>>,
                updated_account: &AccountState<Affine<G0>>,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                leaf_path: CurveTreeWitnessPath<L, G0, G1>,
                account_tree_root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                k_asset_id: Option<F0>,
            ) -> Result<(
                CommonAffirmationHostProof<L, F0, F1, G0, G1>,
                Affine<G0>, // rerandomized_leaf
                F0,         // auth_rerandomization
                F0,         // auth_rand_new_comm
                Affine<G0>, // nullifier
            )> {
                let (protocol, mut even_prover, odd_prover, nullifier) =
                    Self::init::<_, Parameters0, Parameters1>(
                        rng,
                        leg_enc,
                        account,
                        updated_account,
                        updated_account_commitment,
                        leaf_path,
                        account_tree_root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        k_asset_id,
                    )?;
                let rerandomized_leaf = protocol.rerandomized_leaf();
                let auth_rerandomization = protocol.auth_rerandomization();
                let auth_rand_new_comm = protocol.auth_rand_new_comm();
                let challenge = even_prover
                    .transcript()
                    .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
                let host_data = protocol.gen_proof::<_, Parameters0, Parameters1>(
                    &challenge,
                    even_prover,
                    odd_prover,
                    account_tree_params,
                    rng,
                )?;
                Ok((
                    host_data,
                    rerandomized_leaf,
                    auth_rerandomization,
                    auth_rand_new_comm,
                    nullifier,
                ))
            }
        }

        $(#[$proof_attr])*
        #[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
        pub struct $ProofName<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > {
            pub common: CommonAffirmationSplitProof<L, F0, F1, G0, G1>,
        }

        impl<
            const L: usize,
            F0: PrimeField,
            F1: PrimeField,
            G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
            G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
        > $ProofName<L, F0, F1, G0, G1>
        {
            /// Assemble the final split proof from host data and auth proof.
            pub fn assemble(
                host_data: CommonAffirmationHostProof<L, F0, F1, G0, G1>,
                auth_proof: AuthProofAffirmation<Affine<G0>>,
            ) -> Self {
                Self {
                    common: CommonAffirmationSplitProof::assemble(host_data, auth_proof),
                }
            }

            /// Set up BP constraints and write all challenge contributions to transcript.
            /// Returns a `SplitStateChangeVerifier` whose transcript can be used to derive the challenge.
            pub fn challenge_contribution<
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                leg_enc: &LegEncryptionCore<Affine<G0>>,
                eph_pk: &$EphPkType<Affine<G0>>,
            ) -> Result<SplitStateChangeVerifier<L, F0, F1, G0, G1>> {
                let legs_with_conf = vec![LegVerifierConfig {
                    encryption: leg_enc.clone(),
                    party_eph_pk: PartyEphemeralPublicKey::$EphPkVariant(eph_pk.clone()),
                    has_balance_decreased: None,
                    has_counter_decreased: $ver_ctr_dec,
                }];

                SplitStateChangeVerifier::init::<Parameters0, Parameters1>(
                    &self.common,
                    legs_with_conf,
                    updated_account_commitment,
                    nullifier,
                    root,
                    nonce,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                )
            }

            /// Verify all sigma protocols using the externally-derived challenge.
            pub fn verify_and_return_tuples<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                verifier: SplitStateChangeVerifier<L, F0, F1, G0, G1>,
                challenge: &F0,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                rng: &mut R,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
                verifier.verify_sigma_protocols_and_return_tuples(
                    &self.common,
                    None,
                    challenge,
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    rng,
                    rmc,
                )
            }

            /// `challenge_contribution` + challenge derivation + `verify_and_return_tuples`.
            /// Returns `(even_tuple, odd_tuple)`.
            /// Note: `auth_proof` verification is the caller's responsibility (independent Ledger step).
            pub fn verify_with_tuples<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                leg_enc: &LegEncryptionCore<Affine<G0>>,
                eph_pk: &$EphPkType<Affine<G0>>,
                rng: &mut R,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
                let mut verifier = self.challenge_contribution::<Parameters0, Parameters1>(
                    updated_account_commitment,
                    nullifier,
                    root,
                    nonce,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    leg_enc,
                    eph_pk,
                )?;
                let challenge = verifier
                    .even_verifier
                    .as_mut()
                    .unwrap()
                    .transcript()
                    .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
                self.verify_and_return_tuples::<_, Parameters0, Parameters1>(
                    verifier,
                    &challenge,
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    rng,
                    rmc,
                )
            }

            /// Verify only sigma protocols using the externally-derived challenge.
            /// Does not perform R1CS verification; use when batching R1CS separately.
            pub fn verify_sigma_protocols<
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                verifier: SplitStateChangeVerifier<L, F0, F1, G0, G1>,
                challenge: &F0,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
            ) -> Result<()> {
                verifier.verify_sigma_protocols(
                    &self.common,
                    None,
                    challenge,
                    updated_account_commitment,
                    nullifier,
                    account_tree_params,
                    account_comm_key,
                    enc_gen,
                    rmc,
                )
            }

            pub fn verify<
                R: CryptoRngCore,
                Parameters0: DiscreteLogParameters,
                Parameters1: DiscreteLogParameters,
            >(
                &self,
                updated_account_commitment: AccountStateCommitment<Affine<G0>>,
                nullifier: Affine<G0>,
                root: &Root<L, 1, G0, G1>,
                nonce: &[u8],
                account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
                account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
                enc_gen: Affine<G0>,
                leg_enc: &LegEncryptionCore<Affine<G0>>,
                eph_pk: &$EphPkType<Affine<G0>>,
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
                let (even_tuple, odd_tuple) =
                    self.verify_with_tuples::<_, Parameters0, Parameters1>(
                        updated_account_commitment,
                        nullifier,
                        root,
                        nonce,
                        account_tree_params,
                        account_comm_key,
                        enc_gen,
                        leg_enc,
                        eph_pk,
                        rng,
                        rmc_0,
                    )?;
                handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
            }
        }
    };
}

impl_txn_proof! {
    /// This is the proof for "send" txn. Report section 5.1.7
    AffirmAsSenderTxnProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: true,
    prover_has_balance_decreased: true,
    verifier_has_balance_decreased: Some(true),
    verifier_has_counter_decreased: Some(false),
    check_counter_equality: no
}

impl_txn_proof! {
    /// This is the proof for "receive" txn. Report section 5.1.8
    AffirmAsReceiverTxnProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: false,
    verifier_has_counter_decreased: Some(false),
    check_counter_equality: no
}

impl_txn_proof! {
    IrreversibleAffirmAsSenderTxnProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: true,
    prover_has_balance_decreased: true,
    verifier_has_balance_decreased: Some(true),
    verifier_has_counter_decreased: None,
    check_counter_equality: yes
}

impl_txn_proof! {
    IrreversibleAffirmAsReceiverTxnProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: true,
    prover_has_balance_decreased: false,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: None,
    check_counter_equality: yes
}

impl_txn_proof! {
    /// This is the proof for receiver claiming funds from a receive txn. Not present in report
    ClaimReceivedTxnProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: true,
    prover_has_balance_decreased: false,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}

impl_txn_proof! {
    /// Used by sender to reverse his "send" txn and take back his funds
    SenderReverseTxnProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: true,
    prover_has_balance_decreased: false,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}

impl_txn_proof! {
    /// This is the proof for sender sending counter update txn. Report calls it txn_cu
    SenderCounterUpdateTxnProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: false,
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}

impl_txn_proof! {
    /// This is the proof for receiver sending counter update txn.
    ReceiverCounterUpdateTxnProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: false,
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}

impl_txn_split_proof! {
    /// Protocol state for the host in a sender split (W2/W3) affirmation flow.
    AffirmAsSenderSplitProtocol,
    /// Split (Ledger) proof for "send" txn with additive ciphertext decomposition.
    AffirmAsSenderSplitProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: true,
    prover_has_balance_decreased: true,
    verifier_has_balance_decreased: Some(true),
    verifier_has_counter_decreased: Some(false),
    check_counter_equality: no
}

impl_txn_split_proof! {
    /// Protocol state for the host in a receiver split (W2/W3) affirmation flow.
    AffirmAsReceiverSplitProtocol,
    /// Receiver split proof for W2/W3 workflows where host and auth device operate separately.
    AffirmAsReceiverSplitProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: false,
    verifier_has_counter_decreased: Some(false),
    check_counter_equality: no
}

impl_txn_split_proof! {
    IrreversibleAffirmAsSenderSplitProtocol,
    IrreversibleAffirmAsSenderSplitProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: true,
    prover_has_balance_decreased: true,
    verifier_has_balance_decreased: Some(true),
    verifier_has_counter_decreased: None,
    check_counter_equality: yes
}

impl_txn_split_proof! {
    IrreversibleAffirmAsReceiverSplitProtocol,
    IrreversibleAffirmAsReceiverSplitProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: true,
    prover_has_balance_decreased: false,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: None,
    check_counter_equality: yes
}

impl_txn_split_proof! {
    ClaimReceivedSplitProtocol,
    ClaimReceivedSplitProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: true,
    prover_has_balance_decreased: false,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}

impl_txn_split_proof! {
    SenderReverseSplitProtocol,
    SenderReverseSplitProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: true,
    prover_has_balance_decreased: false,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}

impl_txn_split_proof! {
    SenderCounterUpdateSplitProtocol,
    SenderCounterUpdateSplitProof,
    eph_pk_type: SenderEphemeralPublicKey,
    eph_pk_variant: Sender,
    has_balance: false,
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}

impl_txn_split_proof! {
    ReceiverCounterUpdateSplitProtocol,
    ReceiverCounterUpdateSplitProof,
    eph_pk_type: ReceiverEphemeralPublicKey,
    eph_pk_variant: Receiver,
    has_balance: false,
    verifier_has_counter_decreased: Some(true),
    check_counter_equality: no
}
