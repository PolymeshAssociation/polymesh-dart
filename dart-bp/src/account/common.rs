use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, NUM_GENERATORS,
};
use crate::leg::{LegEncryption, LegEncryptionRandomness};
use crate::util::{
    BPProof, add_verification_tuples_to_rmc, enforce_balance_change_prover,
    enforce_balance_change_verifier,
    enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change,
    generate_schnorr_responses_for_balance_change,
    generate_sigma_responses_for_common_state_change, generate_sigma_t_values_for_balance_change,
    generate_sigma_t_values_for_common_state_change, get_verification_tuples_with_rng,
    prove_with_rng, take_challenge_contrib_of_sigma_t_values_for_balance_change,
    verify_given_verification_tuples, verify_sigma_for_balance_change,
    verify_sigma_for_common_state_change,
};
use crate::{
    Error, LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_EVEN_LABEL,
    TXN_ODD_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript, error,
};
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::MerlinTranscript;
use dock_crypto_utils::transcript::Transcript;
use polymesh_dart_common::Balance;
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
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
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
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
    /// Commitment to randomness and response for proving knowledge of asset-id in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_asset_id: Partial1PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of secret key of the party's public key in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_pk: Partial1PokPedersenCommitment<Affine<G0>>,
    /// Commitment to initial rho, old and current rho, old and current randomness
    pub comm_bp_randomness_relations: Affine<G0>,
    /// Commitment to randomness for proving knowledge of above 5 values (step 1 of Schnorr)
    pub t_bp_randomness_relations: Affine<G0>,
    /// Response for proving knowledge of above 5 values (step 3 of Schnorr)
    pub resp_bp_randomness_relations: PartialSchnorrResponse<Affine<G0>>,
}

/// Proof for variables that change only when the account state transition involves a change in account balance
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProof<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: Affine<G0>,
    pub resp_comm_bp_bal: PartialSchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_amount: Partial1PokPedersenCommitment<Affine<G0>>,
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
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    pub leaf_rerandomization: F0,
    #[zeroize(skip)]
    pub nullifier: Affine<G0>,
    pub t_r_leaf: SchnorrCommitment<Affine<G0>>,
    pub t_acc_new: SchnorrCommitment<Affine<G0>>,
    pub t_null: PokDiscreteLogProtocol<Affine<G0>>,
    pub t_leg_asset_id: PokPedersenCommitmentProtocol<Affine<G0>>,
    pub t_leg_pk: PokPedersenCommitmentProtocol<Affine<G0>>,
    #[zeroize(skip)]
    pub comm_bp_randomness_relations: Affine<G0>,
    pub t_bp_randomness_relations: SchnorrCommitment<Affine<G0>>,
    pub comm_bp_blinding: F0,
    pub r_3: F0,
    pub old_balance_blinding: F0,
    pub new_balance_blinding: F0,
}

#[derive(Zeroize, ZeroizeOnDrop)]
pub struct BalanceChangeProver<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub amount: Balance,
    pub old_balance: Balance,
    pub new_balance: Balance,
    pub comm_bp_bal_blinding: G0::ScalarField,
    #[zeroize(skip)]
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: SchnorrCommitment<Affine<G0>>,
    pub t_leg_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
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
    pub prover_is_sender: bool,
    /// Balance can increase, decrease or not change at all
    pub has_balance_decreased: Option<bool>,
    /// Counter can increase, decrease or not change at all
    pub has_counter_decreased: Option<bool>,
}

impl<
    'a,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonStateChangeProver<'a, L, F0, F1, G0, G1>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        is_sender: bool,
        has_balance_changed: bool,
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> error::Result<Self> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            transcript_even,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, transcript_odd);

        let mut prover = Self::init_with_given_prover(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            is_sender,
            has_balance_changed,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )?;
        prover.even_prover = Some(even_prover);
        prover.odd_prover = Some(odd_prover);
        Ok(prover)
    }

    pub fn gen_proof<R: CryptoRngCore>(
        mut self,
        rng: &mut R,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        challenge: &F0,
        account_tree_params: &'a SelRerandParameters<G0, G1>,
    ) -> error::Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
        let even_prover = self.even_prover.take().unwrap();
        let odd_prover = self.odd_prover.take().unwrap();

        let mut proof = self.generate_sigma_responses(account, updated_account, challenge)?;

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params, rng)?;

        proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });
        Ok(proof)
    }

    pub fn init_with_given_prover<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: LegEncryption<Affine<G0>>,
        leg_enc_rand: LegEncryptionRandomness<G0::ScalarField>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        is_sender: bool,
        has_balance_changed: bool,
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> error::Result<Self> {
        ensure_same_accounts(account, updated_account, has_balance_changed)?;

        let (re_randomized_path, leaf_rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
            );

        add_to_transcript!(
            even_prover.transcript(),
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
            NONCE_LABEL,
            nonce,
            LEG_ENC_LABEL,
            leg_enc,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let LegEncryptionRandomness(mut r_1, mut r_2, r_3, mut r_4) = leg_enc_rand;
        let r_pk = if is_sender { r_1 } else { r_2 };

        let mut id_blinding = F0::rand(rng);
        let mut sk_blinding = F0::rand(rng);
        let mut old_counter_blinding = F0::rand(rng);
        let mut asset_id_blinding = F0::rand(rng);
        let mut initial_rho_blinding = F0::rand(rng);
        let mut old_rho_blinding = F0::rand(rng);
        let mut new_rho_blinding = F0::rand(rng);
        let mut old_randomness_blinding = F0::rand(rng);
        let mut new_randomness_blinding = F0::rand(rng);

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
            t_leg_asset_id,
            t_leg_pk,
            t_bp_randomness_relations,
        ) = generate_sigma_t_values_for_common_state_change(
            rng,
            account.asset_id,
            &leg_enc,
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
            asset_id_blinding,
            r_pk,
            r_4,
            even_prover,
            &account_comm_key,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        Zeroize::zeroize(&mut r_1);
        Zeroize::zeroize(&mut r_2);
        Zeroize::zeroize(&mut r_4);
        Zeroize::zeroize(&mut id_blinding);
        Zeroize::zeroize(&mut sk_blinding);
        Zeroize::zeroize(&mut old_counter_blinding);
        Zeroize::zeroize(&mut asset_id_blinding);
        Zeroize::zeroize(&mut initial_rho_blinding);
        Zeroize::zeroize(&mut old_rho_blinding);
        Zeroize::zeroize(&mut new_rho_blinding);
        Zeroize::zeroize(&mut old_randomness_blinding);
        Zeroize::zeroize(&mut new_randomness_blinding);

        Ok(Self {
            even_prover: None,
            odd_prover: None,
            re_randomized_path,
            leaf_rerandomization,
            nullifier,
            t_r_leaf,
            t_acc_new,
            t_null,
            t_leg_asset_id,
            t_leg_pk,
            comm_bp_randomness_relations,
            t_bp_randomness_relations,
            comm_bp_blinding,
            r_3,
            old_balance_blinding,
            new_balance_blinding,
        })
    }

    pub fn generate_sigma_responses(
        mut self,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        challenge: &F0,
    ) -> error::Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
        let (
            resp_leaf,
            resp_acc_new,
            resp_null,
            resp_leg_asset_id,
            resp_leg_pk,
            resp_bp_randomness_relations,
        ) = generate_sigma_responses_for_common_state_change(
            account,
            updated_account,
            self.leaf_rerandomization,
            self.comm_bp_blinding,
            &self.t_r_leaf,
            &self.t_acc_new,
            self.t_null.clone(),
            self.t_leg_asset_id.clone(),
            self.t_leg_pk.clone(),
            &self.t_bp_randomness_relations,
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
            resp_leg_asset_id,
            resp_leg_pk,
            comm_bp_randomness_relations: self.comm_bp_randomness_relations,
            t_bp_randomness_relations: self.t_bp_randomness_relations.t,
            resp_bp_randomness_relations,
        })
    }
}

impl<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy>
    BalanceChangeProver<F0, G0>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        ct_amount: &Affine<G0>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        mut old_balance_blinding: F0,
        mut new_balance_blinding: F0,
        mut r_3: F0,
        has_balance_decreased: bool,
        mut even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> error::Result<Self> {
        ensure_correct_balance_change(account, updated_account, amount, has_balance_decreased)?;
        let (comm_bp_bal_blinding, comm_bp_bal) = enforce_balance_change_prover(
            rng,
            account.balance,
            updated_account.balance,
            amount,
            has_balance_decreased,
            &mut even_prover,
            bp_gens,
        )?;

        let mut transcript = even_prover.transcript();

        let mut amount_blinding = F0::rand(rng);
        let (t_comm_bp_bal, t_leg_amount) = generate_sigma_t_values_for_balance_change(
            rng,
            amount,
            ct_amount,
            old_balance_blinding,
            new_balance_blinding,
            amount_blinding,
            r_3,
            pc_gens,
            bp_gens,
            enc_key_gen,
            enc_gen,
            &mut transcript,
        )?;

        Zeroize::zeroize(&mut old_balance_blinding);
        Zeroize::zeroize(&mut new_balance_blinding);
        Zeroize::zeroize(&mut amount_blinding);
        Zeroize::zeroize(&mut r_3);

        Ok(Self {
            amount,
            old_balance: account.balance,
            new_balance: updated_account.balance,
            comm_bp_bal_blinding,
            comm_bp_bal,
            t_comm_bp_bal,
            t_leg_amount,
        })
    }

    pub fn gen_proof(self, challenge: &F0) -> error::Result<BalanceChangeProof<F0, G0>> {
        let t_comm_bp_bal = self.t_comm_bp_bal.t;
        let (resp_comm_bp_bal, resp_leg_amount) = generate_schnorr_responses_for_balance_change(
            self.amount,
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

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> StateChangeVerifier<L, F0, F1, G0, G1>
{
    /// Takes challenge contributions from all relevant subprotocols
    /// `has_balance_decreased` is None when balance doesn't change
    /// `has_counter_decreased` is None when counter doesn't change
    pub fn init(
        proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        leg_enc: &LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        prover_is_sender: bool,
        has_balance_decreased: Option<bool>,
        has_counter_decreased: Option<bool>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> error::Result<Self> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        let mut verifier = Self::init_with_given_verifier(
            proof,
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            prover_is_sender,
            has_balance_decreased,
            has_counter_decreased,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
        )?;
        verifier.even_verifier = Some(even_verifier);
        verifier.odd_verifier = Some(odd_verifier);
        Ok(verifier)
    }

    /// Enforce Bulletproofs constraints for balance change and takes challenge contributions from balance change related subprotocols
    pub fn enforce_constraints_and_take_challenge_contrib_of_balance_change(
        &mut self,
        proof: &BalanceChangeProof<F0, G0>,
        ct_amount: &Affine<G0>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> error::Result<()> {
        let mut even_verifier = self.even_verifier.take().unwrap();
        self.init_balance_change_verification(
            proof,
            ct_amount,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
        )?;
        self.even_verifier = Some(even_verifier);
        Ok(())
    }

    pub fn verify<R: CryptoRngCore>(
        self,
        rng: &mut R,
        common_state_change_proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        balance_change_proof: Option<&BalanceChangeProof<F0, G0>>,
        challenge: &F0,
        leg_enc: &LegEncryption<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> error::Result<()> {
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
    pub fn verify_sigma_protocols_and_return_tuples<R: CryptoRngCore>(
        mut self,
        common_state_change_proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        balance_change_proof: Option<&BalanceChangeProof<F0, G0>>,
        challenge: &F0,
        leg_enc: &LegEncryption<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> error::Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_verifier = self.even_verifier.take().unwrap();
        let odd_verifier = self.odd_verifier.take().unwrap();

        self.verify_sigma_protocols(
            common_state_change_proof,
            balance_change_proof,
            challenge,
            leg_enc,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
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

    pub fn init_with_given_verifier(
        proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        leg_enc: &LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        prover_is_sender: bool,
        has_balance_decreased: Option<bool>,
        has_counter_decreased: Option<bool>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
    ) -> error::Result<Self> {
        if proof.resp_leaf.len() != (NUM_GENERATORS + 1) {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS + 1,
                proof.resp_leaf.len(),
            ));
        }
        let expected_num_resps = 2 + has_balance_decreased.is_some() as usize;
        if proof.resp_acc_new.responses.len() != expected_num_resps {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                expected_num_resps,
                proof.resp_acc_new.responses.len(),
            ));
        }
        if proof.resp_bp_randomness_relations.responses.len() != 1 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                1,
                proof.resp_bp_randomness_relations.responses.len(),
            ));
        }

        let _ = proof
            .re_randomized_path
            .select_and_rerandomize_verifier_gadget(
                root,
                even_verifier,
                odd_verifier,
                account_tree_params,
            );

        add_to_transcript!(
            even_verifier.transcript(),
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            proof.re_randomized_path,
            NONCE_LABEL,
            nonce,
            LEG_ENC_LABEL,
            leg_enc,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change(
            leg_enc,
            prover_is_sender,
            &nullifier,
            proof.comm_bp_randomness_relations,
            &proof.t_r_leaf,
            &proof.t_acc_new,
            &proof.t_bp_randomness_relations,
            &proof.resp_null,
            &proof.resp_leg_asset_id,
            &proof.resp_leg_pk,
            even_verifier,
            account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;
        // External `Verifier`s will be used to verify this
        Ok(Self {
            even_verifier: None,
            odd_verifier: None,
            prover_is_sender,
            has_counter_decreased,
            has_balance_decreased,
        })
    }

    pub fn init_balance_change_verification(
        &mut self,
        proof: &BalanceChangeProof<F0, G0>,
        ct_amount: &Affine<G0>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    ) -> error::Result<()> {
        if let Some(has_balance_decreased) = self.has_balance_decreased {
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
            enc_key_gen,
            enc_gen,
            &mut verifier_transcript,
        )?;
        Ok(())
    }

    pub fn verify_sigma_protocols(
        self,
        common_state_change_proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        balance_change_proof: Option<&BalanceChangeProof<F0, G0>>,
        challenge: &F0,
        leg_enc: &LegEncryption<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> error::Result<()> {
        let pc_gens = &account_tree_params.even_parameters.pc_gens;
        let bp_gens = &account_tree_params.even_parameters.bp_gens;

        verify_sigma_for_common_state_change(
            leg_enc,
            self.prover_is_sender,
            self.has_counter_decreased,
            balance_change_proof.is_some(),
            &nullifier,
            &common_state_change_proof
                .re_randomized_path
                .get_rerandomized_leaf(),
            &updated_account_commitment.0,
            &common_state_change_proof.comm_bp_randomness_relations,
            &common_state_change_proof.t_r_leaf,
            &common_state_change_proof.t_acc_new,
            &common_state_change_proof.t_bp_randomness_relations,
            &common_state_change_proof.resp_leaf,
            &common_state_change_proof.resp_acc_new,
            &common_state_change_proof.resp_null,
            &common_state_change_proof.resp_leg_asset_id,
            &common_state_change_proof.resp_leg_pk,
            &common_state_change_proof.resp_bp_randomness_relations,
            &challenge,
            account_comm_key,
            pc_gens,
            bp_gens,
            enc_key_gen,
            enc_gen,
            rmc.as_deref_mut(),
        )?;

        if let Some(balance_change_proof) = balance_change_proof {
            verify_sigma_for_balance_change(
                &leg_enc,
                &balance_change_proof.resp_leg_amount,
                &balance_change_proof.comm_bp_bal,
                &balance_change_proof.t_comm_bp_bal,
                &balance_change_proof.resp_comm_bp_bal,
                &challenge,
                common_state_change_proof.resp_leaf.0[1],
                common_state_change_proof.resp_acc_new.responses[&1],
                pc_gens,
                bp_gens,
                enc_key_gen,
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
) -> error::Result<()> {
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
        if old_state.asset_id != new_state.asset_id {
            return Err(Error::ProofGenerationError(
                "Asset ID mismatch between old and new account states".to_string(),
            ));
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
        // Reconsider: Should I be checking such expensive relations
        if old_state.current_rho * old_state.rho != new_state.current_rho {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        if old_state.randomness.square() != new_state.randomness {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        Ok(())
    }
}

pub fn ensure_correct_balance_change<G: AffineRepr>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
    amount: Balance,
    has_balance_decreased: bool,
) -> error::Result<()> {
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
