use std::ops::Neg;
use ark_std::collections::{BTreeMap, BTreeSet};
// use ark_crypto_primitives::crh::poseidon::TwoToOneCRH;
// use ark_crypto_primitives::crh::TwoToOneCRHScheme;
// use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use crate::leg::{LegEncryption, LegEncryptionRandomness};
use crate::poseidon_impls::poseidon_2::Poseidon_hash_2_simple;
use crate::poseidon_impls::poseidon_2::params::Poseidon2Params;
use crate::util::{
    BPProof, add_verification_tuples_to_rmc, bp_gens_for_vec_commitment,
    enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change,
    enforce_constraints_for_randomness_relations, generate_sigma_responses_for_common_state_change,
    generate_sigma_t_values_for_balance_change, generate_sigma_t_values_for_common_state_change,
    take_challenge_contrib_of_sigma_t_values_for_balance_change, verify_sigma_for_balance_change,
    verify_sigma_for_common_state_change,
};
use crate::util::{
    enforce_balance_change_prover, enforce_balance_change_verifier,
    generate_schnorr_responses_for_balance_change, get_verification_tuples_with_rng,
    initialize_curve_tree_prover_with_given_transcripts,
    initialize_curve_tree_verifier_with_given_transcripts, prove_with_rng,
    verify_given_verification_tuples, verify_with_rng,
};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, ASSET_ID_LABEL, BALANCE_LABEL, ID_LABEL, INCREASE_BAL_BY_LABEL,
    LEG_ENC_LABEL, NONCE_LABEL, PK_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL,
    TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript,
};
use crate::{Error, TXN_ODD_LABEL, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::format;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSProof, VerificationTuple, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{
    AssetId, Balance, MAX_ASSET_ID, MAX_BALANCE, NullifierSkGenCounter, PendingTxnCounter,
};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::{Zeroize, ZeroizeOnDrop};

pub const ISSUER_PK_LABEL: &'static [u8; 9] = b"issuer_pk";
pub const COUNTER_LABEL: &'static [u8; 7] = b"counter";
pub const LEGS_LABEL: &'static [u8; 4] = b"legs";
pub const PENDING_SENT_AMOUNT_LABEL: &'static [u8; 19] = b"pending_sent_amount";
pub const PENDING_RECV_AMOUNT_LABEL: &'static [u8; 19] = b"pending_recv_amount";

pub const NUM_GENERATORS: usize = 8;

/// This trait is used to abstract over the account commitment key. It allows us to use different
/// generators for the account commitment key while still providing the same interface.
pub trait AccountCommitmentKeyTrait<G: AffineRepr>: CanonicalSerialize + Clone {
    /// Returns the generator for the signing key.
    fn sk_gen(&self) -> G;

    /// Returns the generator for the balance.
    fn balance_gen(&self) -> G;

    /// Returns the generator for the pending transaction counter.
    fn counter_gen(&self) -> G;

    /// Returns the generator for the asset ID.
    fn asset_id_gen(&self) -> G;

    /// Returns the generator for the original rho value generated during registration
    fn rho_gen(&self) -> G;

    /// Returns the generator for the current rho value. This is used to generate nullifier.
    fn current_rho_gen(&self) -> G;

    /// Returns the generator for the randomness value.
    fn randomness_gen(&self) -> G;

    /// Returns the generator for the user's identity. This is bound to the public key but the relation
    /// between them is not proven in any of the proofs
    fn id_gen(&self) -> G;

    fn as_gens(&self) -> [G; NUM_GENERATORS] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.id_gen(),
        ]
    }

    /// Used for re-randomized leaf
    fn as_gens_with_blinding(&self, blinding: G) -> [G; NUM_GENERATORS + 1] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.id_gen(),
            blinding,
        ]
    }
}

impl<G: AffineRepr> AccountCommitmentKeyTrait<G> for [G; NUM_GENERATORS] {
    fn sk_gen(&self) -> G {
        self[0]
    }

    fn balance_gen(&self) -> G {
        self[1]
    }

    fn counter_gen(&self) -> G {
        self[2]
    }

    fn asset_id_gen(&self) -> G {
        self[3]
    }

    fn rho_gen(&self) -> G {
        self[4]
    }

    fn current_rho_gen(&self) -> G {
        self[5]
    }

    fn randomness_gen(&self) -> G {
        self[6]
    }

    fn id_gen(&self) -> G {
        self[7]
    }
}

// Consider using https://github.com/jymchng/sosecrets-rs for blindings as well as i know how many times the blinding is needed.

#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct AccountState<G: AffineRepr> {
    pub id: G::ScalarField,
    // TODO: Remove this later.
    pub sk: G::ScalarField,
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub asset_id: AssetId,
    pub rho: G::ScalarField,
    pub current_rho: G::ScalarField,
    pub randomness: G::ScalarField,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountStateCommitment<G: AffineRepr>(pub G);

impl<G> AccountState<G>
where
    G: AffineRepr,
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        id: G::ScalarField, // User can hash its string ID onto the field
        sk: G::ScalarField,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        poseidon_config: Poseidon2Params<G::ScalarField>,
    ) -> Result<Self> {
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }
        let combined = Self::concat_asset_id_counter(asset_id, counter);
        let rho = Poseidon_hash_2_simple::<G::ScalarField>(sk, combined, poseidon_config)?;
        let current_rho = rho.square();

        let randomness = G::ScalarField::rand(rng);
        Ok(Self {
            id,
            sk,
            balance: 0,
            counter: 0,
            asset_id,
            rho,
            current_rho,
            randomness,
        })
    }

    /// To be used when using [`RegTxnProofAlt`]
    pub fn new_alt<
        R: CryptoRngCore,
        G2: SWCurveConfig<BaseField = G::ScalarField, ScalarField = G::BaseField>,
    >(
        rng: &mut R,
        id: G::ScalarField,
        sk: G::ScalarField,
        asset_id: AssetId,
        pk_T_gen: Affine<G2>,
    ) -> Result<(Self, G2::ScalarField, G2::ScalarField)> {
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }
        let mut r_1 = G2::ScalarField::rand(rng);
        while r_1.is_zero() {
            r_1 = G2::ScalarField::rand(rng);
        }
        let mut r_2 = G2::ScalarField::rand(rng);
        while r_2.is_zero() {
            r_2 = G2::ScalarField::rand(rng);
        }
        let p_1 = (pk_T_gen * r_1).into_affine();
        let p_2 = (pk_T_gen * r_2).into_affine();
        // r_1 and r_2 can't be 0 so unwrap is fine
        let rho = p_1.x().unwrap();
        let randomness = p_2.x().unwrap();
        let current_rho = rho.square();

        Ok((
            Self {
                id,
                sk,
                balance: 0,
                counter: 0,
                asset_id,
                rho,
                current_rho,
                randomness,
            },
            r_1,
            r_2,
        ))
    }

    pub fn commit(
        &self,
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<AccountStateCommitment<G>> {
        let comm = G::Group::msm(
            &account_comm_key.as_gens()[..],
            &[
                self.sk,
                G::ScalarField::from(self.balance),
                G::ScalarField::from(self.counter),
                G::ScalarField::from(self.asset_id),
                self.rho,
                self.current_rho,
                self.randomness,
                self.id,
            ],
        )
        .map_err(Error::size_mismatch)?;
        Ok(AccountStateCommitment(comm.into_affine()))
    }

    pub fn get_state_for_mint(&self, amount: u64) -> Result<Self> {
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_send(&self, amount: u64) -> Result<Self> {
        if amount > self.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        let mut new_state = self.clone();
        new_state.balance -= amount;
        new_state.counter += 1;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_receive(&self) -> Self {
        let mut new_state = self.clone();
        new_state.counter += 1;
        new_state.refresh_randomness_for_state_change();
        new_state
    }

    pub fn get_state_for_claiming_received(&self, amount: u64) -> Result<Self> {
        if self.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.counter -= 1;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_reversing_send(&self, amount: u64) -> Result<Self> {
        if self.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.counter -= 1;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_decreasing_counter(
        &self,
        decrease_counter_by: Option<PendingTxnCounter>,
    ) -> Result<Self> {
        let decrease_counter_by = decrease_counter_by.unwrap_or(1);
        if self.counter < decrease_counter_by {
            return Err(Error::ProofOfBalanceError(
                "Counter cannot be decreased below zero".to_string(),
            ));
        }
        let mut new_state = self.clone();
        new_state.counter -= decrease_counter_by;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    /// This assumes that an asset either does not have a mediator or mediator cannot reject.
    /// The chain should not allow mediator to reject else a new kind of reverse call has to be
    /// supported
    pub fn get_state_for_irreversible_send(&self, amount: u64) -> Result<Self> {
        if amount > self.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        let mut new_state = self.clone();
        new_state.balance -= amount;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    /// This assumes that an asset either does not have a mediator or mediator cannot reject.
    /// The chain should not allow mediator to reject else a new kind of reverse call has to be
    /// supported
    pub fn get_state_for_irreversible_receive(&self, amount: u64) -> Result<Self> {
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    /// Set rho and commitment randomness to new values. Used as each update to the account state
    /// needs these refreshed.
    pub fn refresh_randomness_for_state_change(&mut self) {
        self.current_rho = self.current_rho * self.rho;
        self.randomness.square_in_place();
    }

    pub fn nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        (comm_key.current_rho_gen() * self.current_rho).into()
    }

    pub(crate) fn initial_nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        (comm_key.rho_gen() * self.rho).into()
    }

    /// Append bytes of counter to bytes of asset id. `combined = asset_id || asset_id`
    /// NOTE: Assumes for correctness, that the concatenation can fit in 64 bytes
    pub(crate) fn concat_asset_id_counter(
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> G::ScalarField {
        let combined: u64 = (asset_id as u64) << 32 | (counter as u64);
        G::ScalarField::from(combined)
    }
}

pub const TXN_POB_LABEL: &[u8; 20] = b"proof-of-balance-txn";

// NOTE: Commitments generated when committing Bulletproofs (using `commit` or `commit_vec`) are already added to the transcript

// Question: This enforces that issuer's secret key (for `issuer_pk`) is the same as the one in the account but does it need to be?
// The issuer should be able to have a separate key for managing issuance txn and account commitment
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MintTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    /// This contains the old account state, but re-randomized (as re-randomized leaf)
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
    /// Commitment to randomness and response for proving knowledge of issuer secret key using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_pk: PokDiscreteLog<Affine<G0>>,
    /// Commitment to the values committed in Bulletproofs
    pub comm_bp: Affine<G0>,
    /// Commitment to randomness for proving knowledge of values committed in Bulletproofs commitment (step 1 of Schnorr)
    pub t_bp: Affine<G0>,
    /// Response for proving knowledge of values committed in Bulletproofs (step 3 of Schnorr)
    pub resp_bp: PartialSchnorrResponse<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MintTxnProof<L, F0, F1, G0, G1>
{
    /// `issuer_pk` has the same secret key as the one in `account`
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        issuer_pk: Affine<G0>,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

        Self::new_with_given_transcript(
            rng,
            issuer_pk,
            increase_bal_by,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            transcript_even,
            transcript_odd,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        issuer_pk: Affine<G0>,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        transcript_even: MerlinTranscript,
        transcript_odd: MerlinTranscript,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_same_accounts(account, updated_account, true)?;
        ensure_correct_balance_change(account, updated_account, increase_bal_by, false)?;
        let (mut even_prover, odd_prover, re_randomized_path, mut rerandomization) =
            initialize_curve_tree_prover_with_given_transcripts(
                rng,
                leaf_path,
                account_tree_params,
                transcript_even,
                transcript_odd,
            );

        let mut transcript = even_prover.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
            NONCE_LABEL,
            nonce,
            ISSUER_PK_LABEL,
            issuer_pk,
            ID_LABEL,
            account.id,
            ASSET_ID_LABEL,
            account.asset_id,
            INCREASE_BAL_BY_LABEL,
            increase_bal_by,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        // We don't need to check if the new balance overflows or not as the chain tracks the total supply
        // (total minted value) and ensures that it is bounded, i.e.<= MAX_AMOUNT

        // Need to prove that:
        // 1. counter is same in both old and new account commitment
        // 2. nullifier and commitment randomness are correctly formed
        // 3. sk in account commitment is the same as in the issuer's public key
        // 4. New balance = old balance + increase_bal_by

        let mut counter_blinding = F0::rand(rng);
        let mut new_balance_blinding = F0::rand(rng);
        let mut initial_rho_blinding = F0::rand(rng);
        let mut old_rho_blinding = F0::rand(rng);
        let mut new_rho_blinding = F0::rand(rng);
        let mut old_s_blinding = F0::rand(rng);
        let mut new_s_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();
        let nullifier = account.nullifier(&account_comm_key);

        // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
        let t_r_leaf = SchnorrCommitment::new(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            vec![
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                old_rho_blinding,
                old_s_blinding,
                F0::rand(rng),
            ],
        );

        // Schnorr commitment for proving correctness of new account state which will become new leaf
        let t_acc_new = SchnorrCommitment::new(
            &Self::acc_new_gens(account_comm_key),
            vec![
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                new_rho_blinding,
                new_s_blinding,
            ],
        );

        // Schnorr commitment for proving correctness of nullifier
        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, old_rho_blinding, &nullifier_gen);

        // Schnorr commitment for knowledge of secret key in public key
        let t_pk = PokDiscreteLogProtocol::init(account.sk, F0::rand(rng), &pk_gen);

        t_r_leaf.challenge_contribution(&mut transcript)?;
        t_acc_new.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;
        t_pk.challenge_contribution(&pk_gen, &issuer_pk, &mut transcript)?;

        // Drop reference to borrow even_prover below
        let _ = transcript;

        let mut comm_bp_blinding = F0::rand(rng);
        let (comm_bp, vars) = even_prover.commit_vec(
            &[
                account.rho,
                account.current_rho,
                updated_account.current_rho,
                account.randomness,
                updated_account.randomness,
            ],
            comm_bp_blinding,
            &account_tree_params.even_parameters.bp_gens,
        );
        enforce_constraints_for_randomness_relations(&mut even_prover, vars);

        let mut transcript = even_prover.transcript();

        let t_bp = SchnorrCommitment::new(
            &Self::bp_gens_vec(account_tree_params),
            vec![
                F0::rand(rng),
                initial_rho_blinding,
                old_rho_blinding,
                new_rho_blinding,
                old_s_blinding,
                new_s_blinding,
            ],
        );

        t_bp.challenge_contribution(&mut transcript)?;

        let prover_challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let mut wits = [
            account.balance.into(),
            account.counter.into(),
            account.rho,
            account.current_rho,
            account.randomness,
            rerandomization,
        ];
        let resp_leaf = t_r_leaf.response(&wits, &prover_challenge)?;
        Zeroize::zeroize(&mut wits);

        // Response for other witnesses will already be generated in sigma protocol for leaf
        let mut wits = BTreeMap::new();
        wits.insert(3, updated_account.current_rho);
        wits.insert(4, updated_account.randomness);
        let resp_acc_new = t_acc_new.partial_response(wits, &prover_challenge)?;

        // Response for witness will already be generated in sigma protocol for leaf
        let resp_null = t_null.gen_partial_proof();

        let resp_pk = t_pk.gen_proof(&prover_challenge);

        // Response for other witnesses will already be generated in sigma protocol for leaf, and new account commitment
        let mut w = BTreeMap::new();
        w.insert(0, comm_bp_blinding);
        let resp_bp = t_bp.partial_response(w, &prover_challenge)?;

        counter_blinding.zeroize();
        new_balance_blinding.zeroize();
        initial_rho_blinding.zeroize();
        old_rho_blinding.zeroize();
        new_rho_blinding.zeroize();
        old_s_blinding.zeroize();
        new_s_blinding.zeroize();
        comm_bp_blinding.zeroize();
        rerandomization.zeroize();

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params, rng)?;

        Ok((
            Self {
                odd_proof,
                even_proof,
                re_randomized_path,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
                resp_leaf,
                resp_acc_new,
                resp_null,
                resp_pk,
                comm_bp,
                t_bp: t_bp.t,
                resp_bp,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        issuer_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
    ) -> Result<()> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

        self.verify_with_given_transcript(
            issuer_pk,
            id,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            rng,
            transcript_even,
            transcript_odd,
        )
    }

    pub fn verify_with_given_transcript<R: CryptoRngCore>(
        &self,
        issuer_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        transcript_even: MerlinTranscript,
        transcript_odd: MerlinTranscript,
    ) -> Result<()> {
        if self.resp_leaf.len() != NUM_GENERATORS - 2 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS - 2,
                self.resp_leaf.len(),
            ));
        }
        if self.resp_acc_new.responses.len() != 2 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                2,
                self.resp_acc_new.responses.len(),
            ));
        }
        if self.resp_bp.responses.len() != 1 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                6,
                self.resp_bp.responses.len(),
            ));
        }
        let (mut even_verifier, odd_verifier) =
            initialize_curve_tree_verifier_with_given_transcripts(
                &self.re_randomized_path,
                root,
                account_tree_params,
                transcript_even,
                transcript_odd,
            );

        let mut verifier_transcript = even_verifier.transcript();

        add_to_transcript!(
            verifier_transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            self.re_randomized_path,
            NONCE_LABEL,
            nonce,
            ISSUER_PK_LABEL,
            issuer_pk,
            ID_LABEL,
            id,
            ASSET_ID_LABEL,
            asset_id,
            INCREASE_BAL_BY_LABEL,
            increase_bal_by,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)?;
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)?;
        self.resp_null.challenge_contribution(
            &nullifier_gen,
            &nullifier,
            &mut verifier_transcript,
        )?;
        self.resp_pk
            .challenge_contribution(&pk_gen, &issuer_pk, &mut verifier_transcript)?;

        // Drop reference to borrow even_verifier below
        let _ = verifier_transcript;

        let vars = even_verifier.commit_vec(5, self.comm_bp);
        enforce_constraints_for_randomness_relations(&mut even_verifier, vars);

        let mut verifier_transcript = even_verifier.transcript();

        self.t_bp.serialize_compressed(&mut verifier_transcript)?;

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let increase_bal_by = F0::from(increase_bal_by);

        let issuer_pk_proj = issuer_pk.into_group();
        let y = self.re_randomized_path.get_rerandomized_leaf()
            - asset_id_comm
            - issuer_pk_proj
            - (account_comm_key.id_gen() * id);
        self.resp_leaf.is_valid(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            &y.into_affine(),
            &self.t_r_leaf,
            &verifier_challenge,
        )?;

        let y = updated_account_commitment.0
            - asset_id_comm
            - issuer_pk_proj
            - (account_comm_key.id_gen() * id)
            - (account_comm_key.balance_gen() * increase_bal_by);
        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(0, self.resp_leaf.0[0]);
        missing_resps.insert(1, self.resp_leaf.0[1]);
        missing_resps.insert(2, self.resp_leaf.0[2]);
        self.resp_acc_new.is_valid(
            &Self::acc_new_gens(account_comm_key),
            &y.into_affine(),
            &self.t_acc_new,
            &verifier_challenge,
            missing_resps,
        )?;

        if !self.resp_null.verify(
            &nullifier,
            &nullifier_gen,
            &verifier_challenge,
            &self.resp_leaf.0[3],
        ) {
            return Err(Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ));
        }
        if !self
            .resp_pk
            .verify(&issuer_pk, &pk_gen, &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "Issuer public key verification failed".to_string(),
            ));
        }

        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(1, self.resp_leaf.0[2]);
        missing_resps.insert(2, self.resp_leaf.0[3]);
        missing_resps.insert(3, self.resp_acc_new.responses[&3]);
        missing_resps.insert(4, self.resp_leaf.0[4]);
        missing_resps.insert(5, self.resp_acc_new.responses[&4]);
        self.resp_bp.is_valid(
            &Self::bp_gens_vec(account_tree_params),
            &self.comm_bp,
            &self.t_bp,
            &verifier_challenge,
            missing_resps,
        )?;

        Ok(verify_with_rng(
            even_verifier,
            odd_verifier,
            &self.even_proof,
            &self.odd_proof,
            &account_tree_params,
            rng,
        )?)
    }

    fn leaf_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        account_tree_params: &SelRerandParameters<G0, G1>,
    ) -> [Affine<G0>; NUM_GENERATORS - 2] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_tree_params.even_parameters.pc_gens.B_blinding,
        ]
    }

    fn acc_new_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> [Affine<G0>; NUM_GENERATORS - 3] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
        ]
    }

    fn bp_gens_vec(account_tree_params: &SelRerandParameters<G0, G1>) -> [Affine<G0>; 6] {
        let mut gens = bp_gens_for_vec_commitment(5, &account_tree_params.even_parameters.bp_gens);
        [
            account_tree_params.even_parameters.pc_gens.B_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ]
    }
}

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
    ) -> Result<Self> {
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
    ) -> Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
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
    ) -> Result<Self> {
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
    ) -> Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
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
    ) -> Result<Self> {
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

    pub fn gen_proof(self, challenge: &F0) -> Result<BalanceChangeProof<F0, G0>> {
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
    ) -> Result<Self> {
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
    ) -> Result<()> {
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
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
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
    ) -> Result<Self> {
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
    ) -> Result<()> {
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
    ) -> Result<()> {
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            true,
            true,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            amount,
            &ct_amount,
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            common_prover.r_3,
            true,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            Some(true),
            Some(false),
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.enforce_constraints_and_take_challenge_contrib_of_balance_change(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            Some(true),
            Some(false),
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            false,
            false,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            None,
            Some(false),
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            None,
            Some(false),
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
            &leg_enc,
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            false,
            true,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            amount,
            &ct_amount,
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            common_prover.r_3,
            false,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            Some(false),
            Some(true),
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.enforce_constraints_and_take_challenge_contrib_of_balance_change(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            Some(false),
            Some(true),
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            true,
            false,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            None,
            Some(true),
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            None,
            Some(true),
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
            &leg_enc,
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            true,
            true,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            amount,
            &ct_amount,
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            common_prover.r_3,
            false,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            Some(false),
            Some(true),
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.enforce_constraints_and_take_challenge_contrib_of_balance_change(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            Some(false),
            Some(true),
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            false,
            false,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            None,
            Some(true),
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            None,
            Some(true),
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
            &leg_enc,
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            true,
            true,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            amount,
            &ct_amount,
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            common_prover.r_3,
            true,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            Some(true),
            None,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.enforce_constraints_and_take_challenge_contrib_of_balance_change(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            Some(true),
            None,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            false,
            true,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            even_prover,
            odd_prover,
        )?;

        let balance_change_prover = BalanceChangeProver::init(
            rng,
            amount,
            &ct_amount,
            account,
            updated_account,
            common_prover.old_balance_blinding,
            common_prover.new_balance_blinding,
            common_prover.r_3,
            false,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            Some(false),
            None,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        verifier.enforce_constraints_and_take_challenge_contrib_of_balance_change(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            Some(false),
            None,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
            even_verifier,
            odd_verifier,
        )?;

        verifier.init_balance_change_verification(
            &self.balance_proof,
            &ct_amount,
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
            &leg_enc,
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

// TODO: PoB can also benefit from RandomizedMultChecker but not doing it for now

/// This is the proof for doing proof of balance with an auditor. This reveals the ID for proof efficiency as the public key is already revealed.
/// Uses Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PobWithAuditorProof<G: AffineRepr> {
    pub nullifier: G,
    pub t_acc: G,
    pub resp_acc: SchnorrResponse<G>,
    pub resp_null: PartialPokDiscreteLog<G>,
    pub resp_pk: PokDiscreteLog<G>,
}

impl<G: AffineRepr> PobWithAuditorProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        Self::new_with_given_transcript(
            rng,
            pk,
            account,
            account_commitment,
            nonce,
            account_comm_key,
            transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: MerlinTranscript,
    ) -> Result<Self> {
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. nullifier is created from current_rho
        //
        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            ID_LABEL,
            account.id,
            PK_LABEL,
            pk
        );

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarField::rand(rng);
        let current_rho_blinding = G::ScalarField::rand(rng);

        // For proving relation g_i * rho + g_j * current_rho + g_k * randomness = C - (pk + g_a * v + g_b * at + g_c * cnt + g_d * id)
        // where C is the account commitment and rho, current_rho and randomness are the witness, rest are instance
        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key.rho_gen(),
                null_gen,
                account_comm_key.randomness_gen(),
            ],
            vec![
                G::ScalarField::rand(rng),
                current_rho_blinding,
                G::ScalarField::rand(rng),
            ],
        );
        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, current_rho_blinding, &null_gen);

        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &pk_gen);

        t_acc.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript)?;
        t_pk.challenge_contribution(&pk_gen, &pk, &mut transcript)?;

        let prover_challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let resp_acc = t_acc.response(
            &[account.rho, account.current_rho, account.randomness],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_partial_proof();
        let resp_pk = t_pk.gen_proof(&prover_challenge);
        Ok(Self {
            nullifier,
            t_acc: t_acc.t,
            resp_acc,
            resp_null,
            resp_pk,
        })
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<()> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        self.verify_with_given_transcript(
            asset_id,
            balance,
            counter,
            id,
            pk,
            account_commitment,
            nonce,
            account_comm_key,
            transcript,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: MerlinTranscript,
    ) -> Result<()> {
        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            ID_LABEL,
            id,
            PK_LABEL,
            pk
        );

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.t_acc.serialize_compressed(&mut transcript)?;
        self.resp_null
            .challenge_contribution(&null_gen, &self.nullifier, &mut transcript)?;
        self.resp_pk
            .challenge_contribution(&pk_gen, &pk, &mut transcript)?;

        let verifier_challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let y = account_commitment.0.into_group()
            - (pk.into_group()
                + account_comm_key.balance_gen() * G::ScalarField::from(balance)
                + account_comm_key.counter_gen() * G::ScalarField::from(counter)
                + account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id)
                + account_comm_key.id_gen() * id);
        self.resp_acc.is_valid(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            &y.into_affine(),
            &self.t_acc,
            &verifier_challenge,
        )?;

        // rho in account matches the one in nullifier
        if !self.resp_null.verify(
            &self.nullifier,
            &null_gen,
            &verifier_challenge,
            &self.resp_acc.0[1],
        ) {
            return Err(Error::ProofVerificationError(
                "Nullifier proof verification failed".to_string(),
            ));
        }
        if !self.resp_pk.verify(&pk, &pk_gen, &verifier_challenge) {
            return Err(Error::ProofVerificationError(
                "Public key proof verification failed".to_string(),
            ));
        }
        Ok(())
    }
}

/// This is the proof for doing proof of balance with an arbitrary party. Report section 5.1.11, fig 10
/// This reveals the ID for proof efficiency as the public key is already revealed.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PobWithAnyoneProof<G: AffineRepr> {
    pub nullifier: G,
    pub t_acc: G,
    pub resp_acc: SchnorrResponse<G>,
    pub resp_null: PartialPokDiscreteLog<G>,
    pub resp_pk: PokDiscreteLog<G>,
    /// For proving correctness of twisted Elgamal ciphertext of asset-id in each leg
    pub asset_id: (G, G::ScalarField),
    /// For proving correctness of twisted Elgamal ciphertext of sender public key. None when prover is sender in no leg.
    pub pk_send: Option<(G, G::ScalarField)>,
    /// For proving correctness of twisted Elgamal ciphertext of receiver public key. None when prover is receiver in no leg.
    pub pk_recv: Option<(G, G::ScalarField)>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is receiver. `\sum{v}` is the total received amount in the legs
    pub resp_recv_amount: Option<PokDiscreteLog<G>>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is sender. `\sum{v}` is the total sent amount in the legs
    pub resp_sent_amount: Option<PokDiscreteLog<G>>,
}

impl<G: AffineRepr> PobWithAnyoneProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        // Next few fields args can be abstracted in a single argument. Like a map with key as index and value as legs, keys, etc for that index
        legs: Vec<(LegEncryption<G>, LegEncryptionRandomness<G::ScalarField>)>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        Self::new_with_given_transcript(
            rng,
            pk,
            account,
            account_commitment,
            legs,
            sender_in_leg_indices,
            receiver_in_leg_indices,
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        // Next few fields args can be abstracted in a single argument. Like a map with key as index and value as legs, keys, etc for that index
        legs: Vec<(LegEncryption<G>, LegEncryptionRandomness<G::ScalarField>)>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<Self> {
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofGenerationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
        }

        let num_pending_txns = legs.len();
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. counter equals number of leg encryptions
        // 3. pk has the respective role in each leg
        // 4. asset-id is the given one in all legs
        // 5. sum of amounts in pending send txns equals the given public value
        // 6. sum of amounts in pending receive txns equals the given public value
        // 7. nullifier is created from current_rho of account commitment

        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. 
        // If its not possible then do a membership proof. Prover could hide the commitment by randomizing it with a new blinding (C' = C + B.r') 

        // Prover has to prove relations of this form for each leg:
        // For sender leg: C_{s, 1} - pk = g * r_{1, i}
        // For receiver leg: C_{r, 1} - pk = g * r_{2, i}
        // For asset-id: C_{at} - h * at = g * r_{4, i}
        // Naively proving, this would lead to 3*n relations for n legs but if we use the batch Schnorr protocol
        // for each of the above 3 relations, we end up with just 3 relations irrespective of number of legs.

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PENDING_SENT_AMOUNT_LABEL,
            pending_sent_amount,
            PENDING_RECV_AMOUNT_LABEL,
            pending_recv_amount,
            ASSET_ID_LABEL,
            account.asset_id,
            BALANCE_LABEL,
            account.balance,
            COUNTER_LABEL,
            account.counter,
            ID_LABEL,
            account.id,
            PK_LABEL,
            pk
        );

        // Add legs separately since it's an array
        for l in &legs {
            transcript.append(LEGS_LABEL, &l.0);
        }

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarField::rand(rng);
        let current_rho_blinding = G::ScalarField::rand(rng);
        let r_1_blinding = (!sender_in_leg_indices.is_empty()).then(|| G::ScalarField::rand(rng));
        let r_2_blinding = (!receiver_in_leg_indices.is_empty()).then(|| G::ScalarField::rand(rng));
        let r_4_blinding = G::ScalarField::rand(rng);

        // Sum of all r_3 where prover is sender
        let mut sum_r_3_sent = G::ScalarField::zero();
        // Sum of all r_3 where prover is receiver
        let mut sum_r_3_recv = G::ScalarField::zero();

        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            vec![
                G::ScalarField::rand(rng),
                current_rho_blinding,
                G::ScalarField::rand(rng),
            ],
        );
        let t_null = PokDiscreteLogProtocol::init(
            account.current_rho,
            current_rho_blinding,
            &account_comm_key.current_rho_gen(),
        );
        // To prove secret key in account state is same as in public key
        let t_pk =
            PokDiscreteLogProtocol::init(account.sk, sk_blinding, &account_comm_key.sk_gen());

        // For proving correctness of twisted Elgamal ciphertext of sender public key. Used when prover is sender in at least 1 leg
        let t_pk_send = r_1_blinding.map(|blinding| (enc_key_gen * blinding).into_affine());
        // For proving correctness of twisted Elgamal ciphertext of receiver public key. Used when prover is receiver in at least 1 leg
        let t_pk_recv = r_2_blinding.map(|blinding| (enc_key_gen * blinding).into_affine());

        // For proving correctness of twisted Elgamal ciphertext of asset-id
        let t_asset_id = (enc_key_gen * r_4_blinding).into_affine();

        // Sum of all C_v where prover is sender
        let mut enc_total_send = G::Group::zero();
        // Sum of all C_v where prover is receiver
        let mut enc_total_recv = G::Group::zero();

        for i in 0..num_pending_txns {
            let LegEncryptionRandomness(_, _, r_3, _) = &legs[i].1;

            if receiver_in_leg_indices.contains(&i) {
                sum_r_3_recv += r_3;
                enc_total_recv += legs[i].0.ct_amount;
            } else if sender_in_leg_indices.contains(&i) {
                sum_r_3_sent += r_3;
                enc_total_send += legs[i].0.ct_amount;
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }
        }

        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is sender. \sum{v} is the total sent amount in the legs
        let t_sent_amount =
            (!sender_in_leg_indices.is_empty()).then(|| PokDiscreteLogProtocol::init(sum_r_3_sent, G::ScalarField::rand(rng), &enc_key_gen));
        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is receiver. \sum{v} is the total received amount in the legs
        let t_recv_amount =
            (!receiver_in_leg_indices.is_empty()).then(|| PokDiscreteLogProtocol::init(sum_r_3_recv, G::ScalarField::rand(rng), &enc_key_gen));

        t_acc.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &nullifier,
            &mut transcript,
        )?;
        t_pk.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript)?;

        t_pk_send.as_ref().map(|t| transcript.append(b"t_pk_send", t));
        t_pk_recv.as_ref().map(|t| transcript.append(b"t_pk_recv", t));
        transcript.append(b"t_asset_id", &t_asset_id);

        if let Some(t) = &t_sent_amount {
            let y = enc_total_send - (enc_gen * G::ScalarField::from(pending_sent_amount));
            t.challenge_contribution(&enc_key_gen, &y.into_affine(), &mut transcript)?;
        }
        if let Some(t) = &t_recv_amount {
            let y = enc_total_recv - (enc_gen * G::ScalarField::from(pending_recv_amount));
            t.challenge_contribution(&enc_key_gen, &y.into_affine(), &mut transcript)?;
        }

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut resp_pk_send = r_1_blinding.map(|blinding| blinding);
        let mut resp_pk_recv = r_2_blinding.map(|blinding| blinding);
        let mut resp_asset_id = r_4_blinding;

        let resp_acc = t_acc.response(
            &[account.rho, account.current_rho, account.randomness],
            &challenge,
        )?;

        // Response for witness will already be generated in sigma protocol for account commitment
        let resp_null = t_null.gen_partial_proof();

        let resp_pk = t_pk.gen_proof(&challenge);

        let mut c = challenge;
        for i in 0..num_pending_txns {
            let LegEncryptionRandomness(r_1, r_2, _, r_4) = &legs[i].1;

            if receiver_in_leg_indices.contains(&i) {
                resp_pk_recv = resp_pk_recv.map(|v| v + (c * r_2));
            } else if sender_in_leg_indices.contains(&i) {
                resp_pk_send = resp_pk_send.map(|v| v + (c * r_1));
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            resp_asset_id += c * r_4;
            c *= challenge;
        }

        let resp_sent_amount = t_sent_amount.map(|t| t.gen_proof(&challenge));
        let resp_recv_amount = t_recv_amount.map(|t| t.gen_proof(&challenge));

        Ok(Self {
            nullifier,
            t_acc: t_acc.t,
            resp_acc,
            resp_null,
            resp_pk,
            asset_id: (t_asset_id, resp_asset_id),
            pk_recv: t_pk_recv.zip(resp_pk_recv),
            pk_send: t_pk_send.zip(resp_pk_send),
            resp_recv_amount,
            resp_sent_amount,
        })
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        legs: Vec<LegEncryption<G>>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<()> {
        let transcript = MerlinTranscript::new(TXN_POB_LABEL);
        self.verify_with_given_transcript(
            asset_id,
            balance,
            counter,
            id,
            pk,
            account_commitment,
            legs,
            sender_in_leg_indices,
            receiver_in_leg_indices,
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            transcript,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        id: G::ScalarField,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        legs: Vec<LegEncryption<G>>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<()> {
        if legs.len() != counter as usize {
            return Err(Error::ProofGenerationError(
                "Number of legs and counter do not match".to_string(),
            ));
        }
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofGenerationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
        }
        if sender_in_leg_indices.len() > 0 {
            if self.pk_send.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for sender indices".to_string(),
                ));
            }
            if self.resp_sent_amount.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for sender amount".to_string(),
                ));
            }
        }
        if receiver_in_leg_indices.len() > 0 {
            if self.pk_recv.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for receiver indices".to_string(),
                ));
            }
            if self.resp_recv_amount.is_none() {
                return Err(Error::ProofVerificationError(
                    "No response for receiver amount".to_string(),
                ));
            }
        }

        let num_pending_txns = legs.len();

        let at = G::ScalarField::from(asset_id);
        let minus_h_at = enc_gen.into_group().neg() * at;

        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PENDING_SENT_AMOUNT_LABEL,
            pending_sent_amount,
            PENDING_RECV_AMOUNT_LABEL,
            pending_recv_amount,
            ASSET_ID_LABEL,
            asset_id,
            BALANCE_LABEL,
            balance,
            COUNTER_LABEL,
            counter,
            ID_LABEL,
            id,
            PK_LABEL,
            pk
        );

        // Add legs separately since it's an array
        for l in &legs {
            transcript.append(LEGS_LABEL, l);
        }

        self.t_acc.serialize_compressed(&mut transcript)?;
        self.resp_null.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &self.nullifier,
            &mut transcript,
        )?;
        self.resp_pk
            .challenge_contribution(&account_comm_key.sk_gen(), pk, &mut transcript)?;

        let mut enc_total_send = G::Group::zero();
        let mut enc_total_recv = G::Group::zero();
        let mut bases_send = Vec::with_capacity(sender_in_leg_indices.len());
        let mut bases_recv = Vec::with_capacity(receiver_in_leg_indices.len());
        let mut bases_at = Vec::with_capacity(legs.len());

        let minus_pk = pk.into_group().neg();
        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_r.into_group() + minus_pk).into_affine();
                enc_total_recv += legs[i].ct_amount;
                bases_recv.push(y);
            } else if sender_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_s.into_group() + minus_pk).into_affine();
                enc_total_send += legs[i].ct_amount;
                bases_send.push(y);
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = (legs[i].ct_asset_id.into_group() + minus_h_at).into_affine();
            bases_at.push(y);
        }

        self.pk_send.as_ref().map(|t| transcript.append(b"t_pk_send", &t.0));
        self.pk_recv.as_ref().map(|t| transcript.append(b"t_pk_recv", &t.0));
        transcript.append(b"t_asset_id", &self.asset_id.0);

        let y_total_send = if let Some(resp) = &self.resp_sent_amount {
            let y_total_send =
                (enc_total_send - (enc_gen * G::ScalarField::from(pending_sent_amount))).into_affine();
            resp.challenge_contribution(
                &enc_key_gen,
                &y_total_send,
                &mut transcript,
            )?;
            Some(y_total_send)
        } else {
            None
        };

        let y_total_recv = if let Some(resp) = &self.resp_recv_amount {
            let y_total_recv =
                (enc_total_recv - (enc_gen * G::ScalarField::from(pending_recv_amount))).into_affine();
            resp.challenge_contribution(
                &enc_key_gen,
                &y_total_recv,
                &mut transcript,
            )?;
            Some(y_total_recv)
        } else {
            None
        };

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let y = account_commitment.0.into_group()
            - (pk.into_group()
                + account_comm_key.balance_gen() * G::ScalarField::from(balance)
                + account_comm_key.counter_gen() * G::ScalarField::from(counter)
                + account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id)
                + account_comm_key.id_gen() * id);
        self.resp_acc.is_valid(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            &y.into_affine(),
            &self.t_acc,
            &challenge,
        )?;

        // rho in account matches the one in nullifier
        if !self.resp_null.verify(
            &self.nullifier,
            &account_comm_key.current_rho_gen(),
            &challenge,
            &self.resp_acc.0[1],
        ) {
            return Err(Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ));
        }

        if !self
            .resp_pk
            .verify(&pk, &account_comm_key.sk_gen(), &challenge)
        {
            return Err(Error::ProofVerificationError(
                "Public key verification failed".to_string(),
            ));
        }

        let mut challenge_powers = vec![];
        let mut c = G::ScalarField::one();
        for _ in 0..num_pending_txns {
            c *= challenge;
            challenge_powers.push(c);
        }

        let mut scalars_send = Vec::with_capacity(sender_in_leg_indices.len());
        let mut scalars_recv = Vec::with_capacity(receiver_in_leg_indices.len());

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                scalars_recv.push(challenge_powers[i]);
            } else if sender_in_leg_indices.contains(&i) {
                scalars_send.push(challenge_powers[i]);
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }
        }

        if let Some((t, resp)) = self.pk_send {
            bases_send.push(enc_key_gen);
            scalars_send.push(-resp);
            if t.into_group().neg() != G::Group::msm_unchecked(&bases_send, &scalars_send) {
                return Err(Error::ProofVerificationError(
                    "Sender public key verification failed".to_string(),
                ));
            }
        }

        if let Some((t, resp)) = self.pk_recv {
            bases_recv.push(enc_key_gen);
            scalars_recv.push(-resp);
            if t.into_group().neg() != G::Group::msm_unchecked(&bases_recv, &scalars_recv) {
                return Err(Error::ProofVerificationError(
                    "Receiver public key verification failed".to_string(),
                ));
            }
        }

        bases_at.push(enc_key_gen);
        challenge_powers.push(-self.asset_id.1);
        if self.asset_id.0.into_group().neg() != G::Group::msm_unchecked(&bases_at, &challenge_powers) {
            return Err(Error::ProofVerificationError(
                "Asset ID verification failed".to_string(),
            ));
        }

        if let Some(resp) = &self.resp_sent_amount {
            if !resp.verify(
                &y_total_send.unwrap(),
                &enc_key_gen,
                &challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    "resp_sent_amount verification failed".to_string(),
                ));
            }
        }

        if let Some(resp) = &self.resp_recv_amount {
            if !resp.verify(
                &y_total_recv.unwrap(),
                &enc_key_gen,
                &challenge,
            ) {
                return Err(Error::ProofVerificationError(
                    "resp_recv_amount verification failed".to_string(),
                ));
            }
        }

        Ok(())
    }
}

fn ensure_same_accounts<G: AffineRepr>(
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

fn ensure_correct_balance_change<G: AffineRepr>(
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

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account_registration::tests::{new_account, setup_comm_key};
    use crate::keys::keygen_sig;
    use crate::leg::tests::setup_keys;
    use crate::leg::{
        AssetCommitmentParams, AssetData, LEG_TXN_EVEN_LABEL, LEG_TXN_ODD_LABEL, Leg,
        LegCreationProof, MEDIATOR_TXN_LABEL, MediatorTxnProof,
    };
    use crate::util::{add_verification_tuples_batches_to_rmc, batch_verify_bp, verify_rmc};
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;

    type PallasFr = ark_pallas::Fr;
    type VestaFr = ark_vesta::Fr;

    fn setup_leg<R: CryptoRngCore>(
        rng: &mut R,
        pk_s: PallasA,
        pk_r: PallasA,
        pk_a_e: PallasA,
        amount: Balance,
        asset_id: AssetId,
        pk_s_e: PallasA,
        pk_r_e: PallasA,
        enc_key_gen: PallasA,
        enc_gen: PallasA,
    ) -> (
        Leg<PallasA>,
        LegEncryption<PallasA>,
        LegEncryptionRandomness<PallasFr>,
    ) {
        let leg = Leg::new(pk_s, pk_r, vec![(true, pk_a_e)], amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(rng, pk_s_e, pk_r_e, enc_key_gen, enc_gen)
            .unwrap();
        (leg, leg_enc, leg_enc_rand)
    }

    /// Create a new tree and add the given account's commitment to the tree and return the tree
    /// In future, allow to generate tree many given number of leaves and add the account commitment to a
    /// random position in tree.
    fn get_tree_with_account_comm<const L: usize>(
        account: &AccountState<PallasA>,
        account_comm_key: impl AccountCommitmentKeyTrait<PallasA>,
        account_tree_params: &SelRerandParameters<PallasParameters, VestaParameters>,
    ) -> Result<CurveTree<L, 1, PallasParameters, VestaParameters>> {
        let account_comm = account.commit(account_comm_key)?;

        // Add account commitment in curve tree
        let set = vec![account_comm.0];
        Ok(
            CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
                &set,
                account_tree_params,
                Some(4),
            ),
        )
    }

    pub fn setup_gens<const NUM_GENS: usize, const L: usize>(
        label: &[u8],
    ) -> (
        SelRerandParameters<PallasParameters, VestaParameters>,
        impl AccountCommitmentKeyTrait<PallasA>,
        PallasA,
        PallasA,
    ) {
        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new_using_label(
                label,
                NUM_GENS as u32,
                NUM_GENS as u32,
            )
            .unwrap();
        let account_comm_key = setup_comm_key(label);
        let enc_key_gen = hash_to_pallas(label, b"enc-key-g").into_affine();
        let enc_gen = hash_to_pallas(label, b"enc-key-h").into_affine();
        (account_tree_params, account_comm_key, enc_key_gen, enc_gen)
    }

    #[test]
    fn increase_supply_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, _, _) = setup_gens::<NUM_GENS, L>(b"testing");

        let asset_id = 1;

        // Issuer creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let id = PallasFr::rand(&mut rng);
        let (account, _, _) = new_account(&mut rng, asset_id, sk_i, id.clone());

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let increase_bal_by = 10;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_mint(increase_bal_by).unwrap();
        assert_eq!(updated_account.balance, account.balance + increase_bal_by);
        assert_eq!(updated_account.rho, account.rho);
        assert_eq!(
            updated_account.current_rho,
            account.current_rho * account.rho
        );
        assert_eq!(updated_account.randomness, account.randomness.square());
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = MintTxnProof::new(
            &mut rng,
            pk_i.0,
            increase_bal_by,
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                pk_i.0,
                id.clone(),
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("For mint txn");
        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );

        assert!(
            proof
                .verify(
                    pk_i.0,
                    id.clone(),
                    asset_id,
                    increase_bal_by + 10, // wrong amount
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    pk_i.0,
                    id.clone(),
                    asset_id,
                    increase_bal_by,
                    updated_account_comm,
                    PallasA::rand(&mut rng), // wrong nullifier
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                )
                .is_err()
        );
    }

    #[test]
    fn send_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        // Setup ends. Sender and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = AffirmAsSenderTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        proof
            .verify(
                &mut rng,
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    }

    #[test]
    fn receive_txn() {
        let mut rng = rand::thread_rng();

        // Setup beings

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        // All parties generate their keys
        let (
            ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;
        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        // Setup ends. Receiver and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_receive();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = AffirmAsReceiverTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        proof
            .verify(
                &mut rng,
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    }

    #[test]
    fn claim_received_funds() {
        // This is what report calls txn_cu (counter update) done by receiver
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        // All parties generate their keys
        let (
            ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
        // Assume that account had some balance and it had sent the receive transaction to increase its counter
        account.balance = 200;
        account.counter += 1;

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_claiming_received(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = ClaimReceivedTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        proof
            .verify(
                &mut rng,
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    }

    #[test]
    fn counter_update_txn_by_sender() {
        // This is similar to receive txn as only account's counter is decreased, balance remains same.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account with non-zero counter
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
        account.balance = 50;
        account.counter = 1;

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = SenderCounterUpdateTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        proof
            .verify(
                &mut rng,
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    }

    #[test]
    fn reverse_send_txn() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
        // Assume that account had some balance and it had sent the send transaction to increase its counter
        account.balance = 200;
        account.counter += 1;

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_reversing_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = SenderReverseTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        proof
            .verify(
                &mut rng,
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    }

    #[test]
    fn reverse_receive_txn() {
        // This is similar to receive txn as only account's counter is decreased, balance remains same.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        // All parties generate their keys
        let (
            ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_leg, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account with non-zero counter
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
        account.balance = 50;
        account.counter = 1;

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = ReceiverCounterUpdateTxnProof::new(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                &mut rng,
                leg_enc.clone(),
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        proof
            .verify(
                &mut rng,
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_key_gen,
                enc_gen,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            prover_time, verifier_time, verifier_time_rmc
        );
    }

    #[test]
    fn pob_with_auditor_as_verifier() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;

        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        // Account exists with some balance and pending txns
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id.clone());
        account.balance = 1000;
        account.counter = 7;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce";

        let proof = PobWithAuditorProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            nonce,
            account_comm_key.clone(),
        )
        .unwrap();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                id,
                &pk.0,
                account_comm,
                nonce,
                account_comm_key,
            )
            .unwrap();
    }

    #[test]
    fn pob_with_anyone() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let enc_key_gen = PallasA::rand(&mut rng);
        let enc_gen = PallasA::rand(&mut rng);

        let (
            ((sk, pk), (_, pk_e)),
            ((_sk_r, pk_other), (_, pk_e_other)),
            ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 20;

        // Account exists with some balance and pending txns
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id.clone());
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // Create some legs as pending transfers
        let mut legs = vec![];
        // Set this amount in each leg. Just for testing, in practice it could be different
        let amount = 10;
        let mut pending_sent_amount = 0;
        let mut pending_recv_amount = 0;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            // for odd i, account is sender, for even i, its receiver
            let (leg_enc, leg_enc_rand) = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg =
                    Leg::new(pk_other.0, pk.0, vec![(true, pk_a_e.0)], amount, asset_id).unwrap();
                let (leg_enc, leg_enc_rand) = leg
                    .encrypt::<_, Blake2b512>(&mut rng, pk_e_other.0, pk_e.0, enc_key_gen, enc_gen)
                    .unwrap();
                (leg_enc, leg_enc_rand)
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg =
                    Leg::new(pk.0, pk_other.0, vec![(true, pk_a_e.0)], amount, asset_id).unwrap();
                let (leg_enc, leg_enc_rand) = leg
                    .encrypt::<_, Blake2b512>(&mut rng, pk_e.0, pk_e_other.0, enc_key_gen, enc_gen)
                    .unwrap();
                (leg_enc, leg_enc_rand)
            };
            legs.push((leg_enc, leg_enc_rand));
        }

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let proof = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                id,
                &pk.0,
                account_comm,
                legs.into_iter().map(|l| l.0).collect(),
                sender_in_leg_indices.clone(),
                receiver_in_leg_indices.clone(),
                pending_sent_amount,
                pending_recv_amount,
                nonce,
                account_comm_key,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("For {num_pending_txns} pending txns");
        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn batch_send_txn_proofs() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 1024;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        let asset_id = 1;
        let amount = 100;
        let batch_size = 10;

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);
        let mut legs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut leg_enc_rands = Vec::with_capacity(batch_size);

        // Generate keys for all parties
        let all_keys: Vec<_> = (0..batch_size)
            .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
            .collect();

        // Create accounts and legs
        let mut account_comms = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let ((sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
            let ((_sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
            let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

            let (leg, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );
            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);

            // Create sender account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s.clone(), id);
            account.balance = 200; // Ensure sufficient balance
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(3),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_send(amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0);

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("batch_send_nonce_{}", i).into_bytes())
            .collect();

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (proof, nullifier) = AffirmAsSenderTxnProof::new(
                &mut rng,
                amount,
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let clock = Instant::now();

        for i in 0..batch_size {
            proofs[i]
                .verify(
                    &mut rng,
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        // These can also be done in parallel
        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

        let batch_verifier_time = clock.elapsed();

        println!(
            "For {batch_size} send txn proofs,, verifier time = {:?}, batch verifier time {:?}",
            verifier_time, batch_verifier_time
        );

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    Some(&mut rmc_0),
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        add_verification_tuples_batches_to_rmc(
            even_tuples,
            odd_tuples,
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let batch_verifier_rmc_time = clock.elapsed();

        println!(
            "For {batch_size} send txn proofs, batch verifier_rmc time {:?}",
            batch_verifier_rmc_time
        );
    }

    #[test]
    fn combined_send_txn_proofs() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 16; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 1024;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        let asset_id = 1;
        let amount = 100;
        let batch_size = 10;

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);
        let mut legs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut leg_enc_rands = Vec::with_capacity(batch_size);

        // Generate keys for all parties
        let all_keys: Vec<_> = (0..batch_size)
            .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
            .collect();

        // Create accounts and legs
        let mut account_comms = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let ((sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
            let ((_sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
            let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

            let (leg, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );
            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);

            // Create sender account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s.clone(), id);
            account.balance = 200; // Ensure sufficient balance
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(3),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_send(amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0);

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("combined_send_nonce_{}", i).into_bytes())
            .collect();

        let clock = Instant::now();
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let (proof, nullifier) = AffirmAsSenderTxnProof::new_with_given_prover(
                &mut rng,
                amount,
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )
            .unwrap();
            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let (even_bp, odd_bp) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params, &mut rng).unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        for i in 0..batch_size {
            proofs[i]
                .enforce_constraints_and_verify_only_sigma_protocols(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut even_verifier,
                    &mut odd_verifier,
                    None,
                )
                .unwrap();
        }

        verify_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let verification_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        for i in 0..batch_size {
            proofs[i]
                .enforce_constraints_and_verify_only_sigma_protocols(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut even_verifier,
                    &mut odd_verifier,
                    Some(&mut rmc_0),
                )
                .unwrap();
        }

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let rmc_verification_time = clock.elapsed();

        println!("Combined send proving time = {:?}", proving_time);
        println!("Combined send verification time = {:?}", verification_time);
        println!(
            "Combined send RMC verification time = {:?}",
            rmc_verification_time
        );
        println!(
            "Combined send proof size = {} bytes",
            even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
        );
    }

    #[test]
    fn batch_receive_txn_proofs() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 1024;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        let asset_id = 1;
        let amount = 100;
        let batch_size = 5;

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);
        let mut legs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut leg_enc_rands = Vec::with_capacity(batch_size);

        // Generate keys for all parties
        let all_keys: Vec<_> = (0..batch_size)
            .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
            .collect();

        // Create accounts and legs
        let mut account_comms = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let ((_sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
            let ((sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
            let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

            let (leg, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );
            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);

            // Create receiver account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r.clone(), id);
            account.balance = 200; // Ensure some initial balance
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(3),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_receive();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0);

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("batch_receive_nonce_{}", i).into_bytes())
            .collect();

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (proof, nullifier) = AffirmAsReceiverTxnProof::new(
                &mut rng,
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let clock = Instant::now();

        for i in 0..batch_size {
            proofs[i]
                .verify(
                    &mut rng,
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    None,
                )
                .unwrap();
        }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        // These can also be done in parallel
        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

        let batch_verifier_time = clock.elapsed();

        println!(
            "For {batch_size} receive txn proofs, verifier time = {:?}, batch verifier time {:?}",
            verifier_time, batch_verifier_time
        );

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut rng,
                    Some(&mut rmc_0),
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        add_verification_tuples_batches_to_rmc(
            even_tuples,
            odd_tuples,
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let batch_verifier_rmc_time = clock.elapsed();

        println!(
            "For {batch_size} receive txn proofs, batch verifier_rmc time {:?}",
            batch_verifier_rmc_time
        );
    }

    #[test]
    fn combined_receive_txn_proofs() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 15;
        const L: usize = 1024;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        let asset_id = 1;
        let amount = 100;
        let batch_size = 5;

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);
        let mut legs = Vec::with_capacity(batch_size);
        let mut leg_encs = Vec::with_capacity(batch_size);
        let mut leg_enc_rands = Vec::with_capacity(batch_size);

        // Generate keys for all parties
        let all_keys: Vec<_> = (0..batch_size)
            .map(|_| setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen))
            .collect();

        // Create accounts and legs
        let mut account_comms = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let ((_sk_s, pk_s), (_sk_s_e, pk_s_e)) = &all_keys[i].0;
            let ((sk_r, pk_r), (_sk_r_e, pk_r_e)) = &all_keys[i].1;
            let ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)) = &all_keys[i].2;

            let (leg, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );
            legs.push(leg);
            leg_encs.push(leg_enc);
            leg_enc_rands.push(leg_enc_rand);

            // Create receiver account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r.clone(), id);
            account.balance = 200; // Ensure some initial balance
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(3),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_receive();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0);

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("combined_receive_nonce_{}", i).into_bytes())
            .collect();

        let clock = Instant::now();
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let (proof, nullifier) = AffirmAsReceiverTxnProof::new_with_given_prover(
                &mut rng,
                leg_encs[i].clone(),
                leg_enc_rands[i].clone(),
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover,
                &mut odd_prover,
            )
            .unwrap();
            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let (even_bp, odd_bp) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params, &mut rng).unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        for i in 0..batch_size {
            proofs[i]
                .enforce_constraints_and_verify_only_sigma_protocols(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut even_verifier,
                    &mut odd_verifier,
                    None,
                )
                .unwrap();
        }

        verify_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let verification_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);
        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        for i in 0..batch_size {
            proofs[i]
                .enforce_constraints_and_verify_only_sigma_protocols(
                    leg_encs[i].clone(),
                    &root,
                    updated_account_comms[i],
                    nullifiers[i],
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    enc_gen,
                    &mut even_verifier,
                    &mut odd_verifier,
                    Some(&mut rmc_0),
                )
                .unwrap();
        }

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &even_bp,
            &odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let rmc_verification_time = clock.elapsed();

        println!("Combined receive proving time = {:?}", proving_time);
        println!(
            "Combined receive verification time = {:?}",
            verification_time
        );
        println!(
            "Combined receive RMC verification time = {:?}",
            rmc_verification_time
        );
        println!(
            "Combined receive proof size = {} bytes",
            even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
        );
    }

    #[test]
    fn single_shot_settlement() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 1024;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        let asset_tree_params = SelRerandParameters {
            even_parameters: account_tree_params.odd_parameters.clone(),
            odd_parameters: account_tree_params.even_parameters.clone(),
        };

        let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        // Create asset commitment parameters
        let asset_comm_params = AssetCommitmentParams::new(
            b"asset-comm-params-for-single-settlement",
            2, // 1 auditor + 1 mediator
            &asset_tree_params.even_parameters.bp_gens,
        );

        // Create AssetData - use auditor key as the sole key
        let keys = vec![(true, pk_a_e.0)]; // Single auditor key
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();

        // Create asset tree with the asset commitment
        let set = vec![asset_data.commitment];
        let asset_tree =
            CurveTree::<L, 1, ark_vesta::VestaConfig, ark_pallas::PallasConfig>::from_leaves(
                &set,
                &asset_tree_params,
                Some(1),
            );

        // Get asset tree path
        let asset_path = asset_tree.get_path_to_leaf_for_proof(0, 0);
        let asset_tree_root = asset_tree.root_node();

        // Create a single leg
        let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create sender account
        let sender_id = PallasFr::rand(&mut rng);
        let (mut sender_account, _, _) = new_account(&mut rng, asset_id, sk_s, sender_id);
        sender_account.balance = 200; // Ensure sufficient balance
        let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

        // Create receiver account
        let receiver_id = PallasFr::rand(&mut rng);
        let (mut receiver_account, _, _) = new_account(&mut rng, asset_id, sk_r, receiver_id);
        receiver_account.balance = 150; // Some initial balance
        let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();

        // Create the account tree with both accounts
        let account_comms = vec![sender_account_comm.0, receiver_account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(2),
        );

        let account_tree_root = account_tree.root_node();

        // Prepare updated account states
        let updated_sender_account = sender_account
            .get_state_for_irreversible_send(amount)
            .unwrap();
        assert_eq!(
            updated_sender_account.balance,
            sender_account.balance - amount
        );
        assert_eq!(updated_sender_account.counter, sender_account.counter);
        let updated_sender_account_comm = updated_sender_account
            .commit(account_comm_key.clone())
            .unwrap();
        let sender_path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let updated_receiver_account = receiver_account
            .get_state_for_irreversible_receive(amount)
            .unwrap();
        assert_eq!(
            updated_receiver_account.balance,
            receiver_account.balance + amount
        );
        assert_eq!(updated_receiver_account.counter, receiver_account.counter);
        let updated_receiver_account_comm = updated_receiver_account
            .commit(account_comm_key.clone())
            .unwrap();
        let receiver_path = account_tree.get_path_to_leaf_for_proof(1, 0);

        let nonce = b"single_shot_settlement_nonce_txn_id_1";

        // Create all three proofs
        let settlement_proof = LegCreationProof::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            asset_path.clone(),
            asset_data,
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let (sender_proof, sender_nullifier) = IrreversibleAffirmAsSenderTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &sender_account,
            &updated_sender_account,
            updated_sender_account_comm,
            sender_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let (receiver_proof, receiver_nullifier) = IrreversibleAffirmAsReceiverTxnProof::new(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &receiver_account,
            &updated_receiver_account,
            updated_receiver_account_comm,
            receiver_path.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let start = Instant::now();

        // All 3 can be verified in parallel
        let (settlement_even, settlement_odd) = settlement_proof
            .verify_and_return_tuples(
                leg_enc.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let (sender_even, sender_odd) = sender_proof
            .verify_and_return_tuples(
                leg_enc.clone(),
                &account_tree_root,
                updated_sender_account_comm,
                sender_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let (receiver_even, receiver_odd) = receiver_proof
            .verify_and_return_tuples(
                leg_enc.clone(),
                &account_tree_root,
                updated_receiver_account_comm,
                receiver_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                None,
            )
            .unwrap();

        // Asset tree uses opposite curves than account tree so merging accordingly
        let even_tuples = vec![settlement_odd, sender_even, receiver_even];
        let odd_tuples = vec![settlement_even, sender_odd, receiver_odd];

        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

        let verifier_time = start.elapsed();

        let start = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let (settlement_even, settlement_odd) = settlement_proof
            .verify_and_return_tuples(
                leg_enc.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut rng,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (sender_even, sender_odd) = sender_proof
            .verify_and_return_tuples(
                leg_enc.clone(),
                &account_tree_root,
                updated_sender_account_comm,
                sender_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (receiver_even, receiver_odd) = receiver_proof
            .verify_and_return_tuples(
                leg_enc.clone(),
                &account_tree_root,
                updated_receiver_account_comm,
                receiver_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut rng,
                Some(&mut rmc_0),
            )
            .unwrap();

        // Asset tree uses opposite curves than account tree so merging accordingly
        let even_tuples = vec![settlement_odd, sender_even, receiver_even];
        let odd_tuples = vec![settlement_even, sender_odd, receiver_odd];

        add_verification_tuples_batches_to_rmc(
            even_tuples,
            odd_tuples,
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
        let verifier_rmc_time = start.elapsed();

        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time, verifier_rmc_time
        );
    }

    #[test]
    fn swap_settlement() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 2;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        let asset_tree_params = SelRerandParameters {
            even_parameters: account_tree_params.odd_parameters.clone(),
            odd_parameters: account_tree_params.even_parameters.clone(),
        };

        let asset_comm_params = AssetCommitmentParams::new(
            b"asset-comm-params",
            1,
            &asset_tree_params.even_parameters.bp_gens,
        );

        // Setup keys for sender, receiver, and auditor
        let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (sk_m_e, pk_m_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        // Two different asset-ids for swap
        let asset_id_1 = 1;
        let asset_id_2 = 2;
        let amount_1 = 100;
        let amount_2 = 200;

        // Both assets have same mediator
        let keys = vec![(false, pk_m_e.0)];
        let asset_data_1 = AssetData::new(
            asset_id_1,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();
        let asset_data_2 = AssetData::new(
            asset_id_2,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();

        let set = vec![asset_data_1.commitment, asset_data_2.commitment];
        let asset_tree =
            CurveTree::<L, 1, ark_vesta::VestaConfig, ark_pallas::PallasConfig>::from_leaves(
                &set,
                &asset_tree_params,
                Some(2),
            );
        let asset_path_1 = asset_tree.get_path_to_leaf_for_proof(0, 0);
        let asset_path_2 = asset_tree.get_path_to_leaf_for_proof(1, 0);
        let asset_tree_root = asset_tree.root_node();

        // Create two legs for swap
        let leg_1 = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount_1, asset_id_1).unwrap();
        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();
        let leg_2 = Leg::new(pk_r.0, pk_s.0, keys.clone(), amount_2, asset_id_2).unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_r_e.0, pk_s_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Alice has accounts for both assets
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_s.clone(), alice_id);
        alice_account_1.balance = 200;
        let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

        let (mut alice_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_s.clone(), alice_id);
        alice_account_2.balance = 50;
        let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

        // Bob has accounts for both assets
        let bob_id = PallasFr::rand(&mut rng);
        let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_r.clone(), bob_id);
        bob_account_1.balance = 50;
        let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

        let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_r, bob_id);
        bob_account_2.balance = 300;
        let bob_account_comm_2 = bob_account_2.commit(account_comm_key.clone()).unwrap();

        // Account tree for all four accounts
        let account_comms = vec![
            alice_account_comm_1.0,
            alice_account_comm_2.0,
            bob_account_comm_1.0,
            bob_account_comm_2.0,
        ];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(4),
        );
        let account_tree_root = account_tree.root_node();

        // Prepare updated account states
        let updated_alice_account_1 = alice_account_1.get_state_for_send(amount_1).unwrap();
        let updated_alice_account_comm_1 = updated_alice_account_1
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0);

        let updated_alice_account_2 = alice_account_2.get_state_for_receive();
        let updated_alice_account_comm_2 = updated_alice_account_2
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0);

        let updated_bob_account_1 = bob_account_1.get_state_for_receive();
        let updated_bob_account_comm_1 = updated_bob_account_1
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0);

        let updated_bob_account_2 = bob_account_2.get_state_for_send(amount_2).unwrap();
        let updated_bob_account_comm_2 = updated_bob_account_2
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0);

        let nonce = b"swap_settlement_nonce_txn_id_1";

        // Combined settlement proofs for both legs
        let clock = Instant::now();
        let even_transcript_settlement = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript_settlement = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover_settlement = Prover::new(
            &asset_tree_params.even_parameters.pc_gens,
            even_transcript_settlement,
        );
        let mut odd_prover_settlement = Prover::new(
            &asset_tree_params.odd_parameters.pc_gens,
            odd_transcript_settlement,
        );

        let settlement_proof_1 = LegCreationProof::new_with_given_prover(
            &mut rng,
            leg_1.clone(),
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            asset_path_1.clone(),
            asset_data_1,
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_prover_settlement,
            &mut odd_prover_settlement,
        )
        .unwrap();

        let settlement_proof_2 = LegCreationProof::new_with_given_prover(
            &mut rng,
            leg_2.clone(),
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            asset_path_2.clone(),
            asset_data_2,
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_prover_settlement,
            &mut odd_prover_settlement,
        )
        .unwrap();

        let (settlement_even_bp, settlement_odd_bp) = prove_with_rng(
            even_prover_settlement,
            odd_prover_settlement,
            &asset_tree_params,
            &mut rng,
        )
        .unwrap();
        let settlement_proving_time = clock.elapsed();

        // Verify settlement proofs (both legs)
        let clock = Instant::now();

        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut settlement_even_verifier = Verifier::new(transcript_even);
        let mut settlement_odd_verifier = Verifier::new(transcript_odd);

        settlement_proof_1
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_1.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                None,
            )
            .unwrap();

        settlement_proof_2
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_2.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                None,
            )
            .unwrap();

        verify_with_rng(
            settlement_even_verifier,
            settlement_odd_verifier,
            &settlement_even_bp,
            &settlement_odd_bp,
            &asset_tree_params,
            &mut rng,
        )
        .unwrap();
        let settlement_verification_time = clock.elapsed();

        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        // Verify settlement proofs (both legs)
        let clock = Instant::now();

        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut settlement_even_verifier = Verifier::new(transcript_even);
        let mut settlement_odd_verifier = Verifier::new(transcript_odd);

        settlement_proof_1
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_1.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        settlement_proof_2
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_2.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            settlement_even_verifier,
            settlement_odd_verifier,
            &settlement_even_bp,
            &settlement_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &asset_tree_params,
            &mut rmc_1,
            &mut rmc_0,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let settlement_verification_time_rmc = clock.elapsed();

        // Mediator affirms both legs with a single proof
        let clock = Instant::now();
        let accept = true;
        // Mediator is at index 0 in both assets
        let index_in_asset_data = 0;

        // This could be made a bit faster and shorter if prover was willing to prove that same secret
        // key is used. But this might not be the setting in practice.

        // Create shared transcript for mediator proof covering both legs
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

        let med_proof_1 = MediatorTxnProof::new_with_given_transcript(
            &mut rng,
            leg_enc_1.clone(),
            asset_id_1,
            sk_m_e.0,
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
        )
        .unwrap();

        let med_proof_2 = MediatorTxnProof::new_with_given_transcript(
            &mut rng,
            leg_enc_2.clone(),
            asset_id_2,
            sk_m_e.0,
            accept,
            index_in_asset_data,
            nonce,
            enc_gen,
            &mut transcript,
        )
        .unwrap();

        let mediator_proving_time = clock.elapsed();

        let clock = Instant::now();
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);

        med_proof_1
            .verify_with_given_transcript(
                leg_enc_1.clone(),
                accept,
                index_in_asset_data,
                nonce,
                enc_gen,
                &mut transcript,
                None,
            )
            .unwrap();

        med_proof_2
            .verify_with_given_transcript(
                leg_enc_2.clone(),
                accept,
                index_in_asset_data,
                nonce,
                enc_gen,
                &mut transcript,
                None,
            )
            .unwrap();

        let mediator_verification_time = clock.elapsed();

        let clock = Instant::now();
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        let mut rmc_med = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        med_proof_1
            .verify_with_given_transcript(
                leg_enc_1.clone(),
                accept,
                index_in_asset_data,
                nonce,
                enc_gen,
                &mut transcript,
                Some(&mut rmc_med),
            )
            .unwrap();

        med_proof_2
            .verify_with_given_transcript(
                leg_enc_2.clone(),
                accept,
                index_in_asset_data,
                nonce,
                enc_gen,
                &mut transcript,
                Some(&mut rmc_med),
            )
            .unwrap();

        assert!(rmc_med.verify());

        let mediator_verification_time_rmc = clock.elapsed();

        // Combined alice proofs for both legs (alice sends in leg1, receives in leg2)
        let clock = Instant::now();
        let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_alice = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_alice,
        );
        let mut odd_prover_alice = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_alice,
        );

        // Alice proof for leg1 (sending asset1)
        let (alice_proof_leg1, alice_nullifier_leg1) =
            AffirmAsSenderTxnProof::new_with_given_prover(
                &mut rng,
                amount_1,
                leg_enc_1.clone(),
                leg_enc_rand_1.clone(),
                &alice_account_1,
                &updated_alice_account_1,
                updated_alice_account_comm_1,
                alice_path_1.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        // Alice proof for leg2 (receiving asset2)
        let (alice_proof_leg2, alice_nullifier_leg2) =
            AffirmAsReceiverTxnProof::new_with_given_prover(
                &mut rng,
                leg_enc_2.clone(),
                leg_enc_rand_2.clone(),
                &alice_account_2,
                &updated_alice_account_2,
                updated_alice_account_comm_2,
                alice_path_2.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        let (alice_even_bp, alice_odd_bp) = prove_with_rng(
            even_prover_alice,
            odd_prover_alice,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let alice_proving_time = clock.elapsed();

        // Combined bob proofs for both legs (bob receives leg1, sends leg2)
        let clock = Instant::now();
        let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_bob = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_bob,
        );
        let mut odd_prover_bob = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_bob,
        );

        // Bob proof for leg1 (receiving asset1)
        let (bob_proof_leg1, bob_nullifier_leg1) = AffirmAsReceiverTxnProof::new_with_given_prover(
            &mut rng,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            &bob_account_1,
            &updated_bob_account_1,
            updated_bob_account_comm_1,
            bob_path_1.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

        // Bob proof for leg2 (sending asset2)
        let (bob_proof_leg2, bob_nullifier_leg2) = AffirmAsSenderTxnProof::new_with_given_prover(
            &mut rng,
            amount_2,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            &bob_account_2,
            &updated_bob_account_2,
            updated_bob_account_comm_2,
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

        let (bob_even_bp, bob_odd_bp) = prove_with_rng(
            even_prover_bob,
            odd_prover_bob,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let bob_proving_time = clock.elapsed();

        // Verify alice proofs (both legs)
        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_1,
                alice_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        alice_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_2,
                alice_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        verify_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let alice_verification_time = clock.elapsed();

        // Verify bob proofs (both legs)
        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        bob_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_1,
                bob_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        bob_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_2,
                bob_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        verify_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let bob_verification_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_1,
                alice_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        alice_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_2,
                alice_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let alice_verification_time_rmc = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        bob_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_1,
                bob_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        bob_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_2,
                bob_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let bob_verification_time_rmc = clock.elapsed();

        // Counter update proofs
        // Alice: ClaimReceivedTxnProof for alice_account_2 (receiving leg2), SenderCounterUpdateTxnProof for alice_account_1 (sending leg1)
        // Bob: ClaimReceivedTxnProof for bob_account_1 (receiving leg1), SenderCounterUpdateTxnProof for bob_account_2 (sending leg2)

        // Alice updates
        let updated_alice_account_3 = updated_alice_account_2
            .get_state_for_claiming_received(amount_2)
            .unwrap();
        let updated_alice_account_comm_3 = updated_alice_account_3
            .commit(account_comm_key.clone())
            .unwrap();

        let updated_alice_account_4 = updated_alice_account_1
            .get_state_for_decreasing_counter(None)
            .unwrap();
        let updated_alice_account_comm_4 = updated_alice_account_4
            .commit(account_comm_key.clone())
            .unwrap();

        // Bob updates
        let updated_bob_account_3 = updated_bob_account_1
            .get_state_for_claiming_received(amount_1)
            .unwrap();
        let updated_bob_account_comm_3 = updated_bob_account_3
            .commit(account_comm_key.clone())
            .unwrap();

        let updated_bob_account_4 = updated_bob_account_2
            .get_state_for_decreasing_counter(None)
            .unwrap();
        let updated_bob_account_comm_4 = updated_bob_account_4
            .commit(account_comm_key.clone())
            .unwrap();

        // In practice, existing tree will be updated
        let account_comms = vec![
            alice_account_comm_1.0,
            alice_account_comm_2.0,
            bob_account_comm_1.0,
            bob_account_comm_2.0,
            updated_alice_account_comm_1.0,
            updated_alice_account_comm_2.0,
            updated_bob_account_comm_1.0,
            updated_bob_account_comm_2.0,
        ];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(4),
        );
        let account_tree_root = account_tree.root_node();

        let alice_1_path = account_tree.get_path_to_leaf_for_proof(4, 0);
        let alice_2_path = account_tree.get_path_to_leaf_for_proof(5, 0);
        let bob_1_path = account_tree.get_path_to_leaf_for_proof(6, 0);
        let bob_2_path = account_tree.get_path_to_leaf_for_proof(7, 0);

        // Counter update proofs
        // Alice counter update proving
        let clock = Instant::now();

        // Alice counter updates with her own provers
        let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_alice = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_alice,
        );
        let mut odd_prover_alice = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_alice,
        );

        let (alice_counter_update_proof, alice_cu_nullifier) =
            SenderCounterUpdateTxnProof::new_with_given_prover(
                &mut rng,
                leg_enc_1.clone(),
                leg_enc_rand_1.clone(),
                &updated_alice_account_1,
                &updated_alice_account_4,
                updated_alice_account_comm_4,
                alice_1_path,
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        let (alice_claim_proof, alice_claim_nullifier) =
            ClaimReceivedTxnProof::new_with_given_prover(
                &mut rng,
                amount_2,
                leg_enc_2.clone(),
                leg_enc_rand_2.clone(),
                &updated_alice_account_2,
                &updated_alice_account_3,
                updated_alice_account_comm_3,
                alice_2_path,
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        let (alice_even_bp, alice_odd_bp) = prove_with_rng(
            even_prover_alice,
            odd_prover_alice,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();

        let alice_counter_update_proving_time = clock.elapsed();

        // Bob counter update proving
        let clock = Instant::now();

        // Bob counter updates with his own provers
        let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_bob = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_bob,
        );
        let mut odd_prover_bob = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_bob,
        );

        let (bob_claim_proof, bob_claim_nullifier) = ClaimReceivedTxnProof::new_with_given_prover(
            &mut rng,
            amount_1,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            &updated_bob_account_1,
            &updated_bob_account_3,
            updated_bob_account_comm_3,
            bob_1_path,
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

        let (bob_counter_update_proof, bob_cu_nullifier) =
            SenderCounterUpdateTxnProof::new_with_given_prover(
                &mut rng,
                leg_enc_2.clone(),
                leg_enc_rand_2.clone(),
                &updated_bob_account_2,
                &updated_bob_account_4,
                updated_bob_account_comm_4,
                bob_2_path,
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_bob,
                &mut odd_prover_bob,
            )
            .unwrap();

        let (bob_even_bp, bob_odd_bp) = prove_with_rng(
            even_prover_bob,
            odd_prover_bob,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();

        let bob_counter_update_proving_time = clock.elapsed();

        // Verify counter update proofs
        // Alice counter update verification
        let clock = Instant::now();

        // Verify Alice counter update proofs
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_counter_update_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_4,
                alice_cu_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        alice_claim_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_3,
                alice_claim_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        verify_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();

        let alice_counter_update_verification_time = clock.elapsed();

        // Bob counter update verification
        let clock = Instant::now();

        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        // Verify Bob counter update proofs
        bob_claim_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_3,
                bob_claim_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        bob_counter_update_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_4,
                bob_cu_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        verify_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();

        let bob_counter_update_verification_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_counter_update_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_4,
                alice_cu_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        alice_claim_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_3,
                alice_claim_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let alice_counter_update_verification_time_rmc = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        // Verify Bob counter update proofs
        bob_claim_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_3,
                bob_claim_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        bob_counter_update_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_4,
                bob_cu_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let bob_counter_update_verification_time_rmc = clock.elapsed();

        let settlement_proof_size = settlement_even_bp.compressed_size()
            + settlement_odd_bp.compressed_size()
            + settlement_proof_1.compressed_size()
            + settlement_proof_2.compressed_size();
        let mediator_proof_size = med_proof_1.compressed_size() + med_proof_2.compressed_size();
        let alice_affirmation_proof_size = alice_even_bp.compressed_size()
            + alice_odd_bp.compressed_size()
            + alice_proof_leg1.compressed_size()
            + alice_proof_leg2.compressed_size();
        let alice_counter_update_proof_size = alice_even_bp.compressed_size()
            + alice_odd_bp.compressed_size()
            + alice_claim_proof.compressed_size()
            + alice_counter_update_proof.compressed_size();
        let bob_affirmation_proof_size = bob_even_bp.compressed_size()
            + bob_odd_bp.compressed_size()
            + bob_proof_leg1.compressed_size()
            + bob_proof_leg2.compressed_size();
        let bob_counter_update_proof_size = bob_even_bp.compressed_size()
            + bob_odd_bp.compressed_size()
            + bob_claim_proof.compressed_size()
            + bob_counter_update_proof.compressed_size();

        println!(
            "Settlement proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            settlement_proving_time,
            settlement_verification_time,
            settlement_verification_time_rmc,
            settlement_proof_size
        );
        println!(
            "Mediator affirmation proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            mediator_proving_time,
            mediator_verification_time,
            mediator_verification_time_rmc,
            mediator_proof_size
        );
        println!(
            "Alice affirmation proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            alice_proving_time,
            alice_verification_time,
            alice_verification_time_rmc,
            alice_affirmation_proof_size
        );
        println!(
            "Alice counter update proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            alice_counter_update_proving_time,
            alice_counter_update_verification_time,
            alice_counter_update_verification_time_rmc,
            alice_counter_update_proof_size
        );
        println!(
            "Bob affirmation proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            bob_proving_time,
            bob_verification_time,
            bob_verification_time_rmc,
            bob_affirmation_proof_size
        );
        println!(
            "Bob counter update proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            bob_counter_update_proving_time,
            bob_counter_update_verification_time,
            bob_counter_update_verification_time_rmc,
            bob_counter_update_proof_size
        );
    }

    #[test]
    fn reverse_settlement() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 2;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        // Setup keys for sender, receiver, and auditor
        let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        // Two different asset-ids for swap
        let asset_id_1 = 1;
        let asset_id_2 = 2;
        let amount_1 = 100;
        let amount_2 = 200;

        let keys = vec![(true, pk_a_e.0)];
        // Create two legs for swap
        let leg_1 = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount_1, asset_id_1).unwrap();
        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();
        let leg_2 = Leg::new(pk_r.0, pk_s.0, keys.clone(), amount_2, asset_id_2).unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_r_e.0, pk_s_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Alice has accounts for both assets
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_s.clone(), alice_id);
        alice_account_1.balance = 500;
        alice_account_1.counter = 1;
        let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

        let (mut alice_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_s.clone(), alice_id);
        alice_account_2.balance = 50;
        alice_account_2.counter = 1;
        let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

        // Bob has accounts for both assets
        let bob_id = PallasFr::rand(&mut rng);
        let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_r.clone(), bob_id);
        bob_account_1.balance = 500;
        bob_account_1.counter = 1;
        let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

        let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_r.clone(), bob_id);
        bob_account_2.balance = 50;
        bob_account_2.counter = 1;
        let bob_account_comm_2 = bob_account_2.commit(account_comm_key.clone()).unwrap();

        // Account tree for all four accounts
        let account_comms = vec![
            alice_account_comm_1.0,
            alice_account_comm_2.0,
            bob_account_comm_1.0,
            bob_account_comm_2.0,
        ];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(4),
        );
        let account_tree_root = account_tree.root_node();

        // Prepare updated account states
        let updated_alice_account_1 = alice_account_1
            .get_state_for_reversing_send(amount_1)
            .unwrap();
        let updated_alice_account_comm_1 = updated_alice_account_1
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0);

        let updated_alice_account_2 = alice_account_2
            .get_state_for_decreasing_counter(None)
            .unwrap();
        let updated_alice_account_comm_2 = updated_alice_account_2
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0);

        let updated_bob_account_1 = bob_account_1
            .get_state_for_decreasing_counter(None)
            .unwrap();
        let updated_bob_account_comm_1 = updated_bob_account_1
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0);

        let updated_bob_account_2 = bob_account_2
            .get_state_for_reversing_send(amount_2)
            .unwrap();
        let updated_bob_account_comm_2 = updated_bob_account_2
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0);

        let nonce = b"reverse_settlement_nonce_txn_id_1";

        // Combined alice proofs for both legs (alice reverses send in leg1, reverses receive in leg2)
        let clock = Instant::now();
        let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_alice = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_alice,
        );
        let mut odd_prover_alice = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_alice,
        );

        // Alice proof for leg1 (reverse sending asset1)
        let (alice_proof_leg1, alice_nullifier_leg1) =
            SenderReverseTxnProof::new_with_given_prover(
                &mut rng,
                amount_1,
                leg_enc_1.clone(),
                leg_enc_rand_1.clone(),
                &alice_account_1,
                &updated_alice_account_1,
                updated_alice_account_comm_1,
                alice_path_1.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        // Alice proof for leg2 (reverse receiving asset2)
        let (alice_proof_leg2, alice_nullifier_leg2) =
            ReceiverCounterUpdateTxnProof::new_with_given_prover(
                &mut rng,
                leg_enc_2.clone(),
                leg_enc_rand_2.clone(),
                &alice_account_2,
                &updated_alice_account_2,
                updated_alice_account_comm_2,
                alice_path_2.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        let (alice_even_bp, alice_odd_bp) = prove_with_rng(
            even_prover_alice,
            odd_prover_alice,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let alice_proving_time = clock.elapsed();

        // Combined bob proofs for both legs (bob reverses receive in leg1, reverses send in leg2)
        let clock = Instant::now();
        let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_bob = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_bob,
        );
        let mut odd_prover_bob = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_bob,
        );

        // Bob proof for leg1 (reverse receiving asset1)
        let (bob_proof_leg1, bob_nullifier_leg1) =
            ReceiverCounterUpdateTxnProof::new_with_given_prover(
                &mut rng,
                leg_enc_1.clone(),
                leg_enc_rand_1.clone(),
                &bob_account_1,
                &updated_bob_account_1,
                updated_bob_account_comm_1,
                bob_path_1.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_bob,
                &mut odd_prover_bob,
            )
            .unwrap();

        // Bob proof for leg2 (reverse sending asset2)
        let (bob_proof_leg2, bob_nullifier_leg2) = SenderReverseTxnProof::new_with_given_prover(
            &mut rng,
            amount_2,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            &bob_account_2,
            &updated_bob_account_2,
            updated_bob_account_comm_2,
            bob_path_2.clone(),
            &account_tree_root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            &mut even_prover_bob,
            &mut odd_prover_bob,
        )
        .unwrap();

        let (bob_even_bp, bob_odd_bp) = prove_with_rng(
            even_prover_bob,
            odd_prover_bob,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let bob_proving_time = clock.elapsed();

        // Verify alice proofs (both legs)
        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_1,
                alice_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        alice_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_2,
                alice_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        verify_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let alice_verification_time = clock.elapsed();

        // Verify bob proofs (both legs)
        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        bob_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_1,
                bob_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        bob_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_2,
                bob_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        verify_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();
        let bob_verification_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_1,
                alice_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        alice_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_2,
                alice_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let alice_verification_time_rmc = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        bob_proof_leg1
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_1,
                bob_nullifier_leg1,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        bob_proof_leg2
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_2,
                bob_nullifier_leg2,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_rmc, odd_tuple_rmc) = get_verification_tuples_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![even_tuple_rmc],
            vec![odd_tuple_rmc],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let bob_verification_time_rmc = clock.elapsed();

        let alice_affirmation_proof_size = alice_even_bp.compressed_size()
            + alice_odd_bp.compressed_size()
            + alice_proof_leg1.compressed_size()
            + alice_proof_leg2.compressed_size();

        let bob_affirmation_proof_size = bob_even_bp.compressed_size()
            + bob_odd_bp.compressed_size()
            + bob_proof_leg1.compressed_size()
            + bob_proof_leg2.compressed_size();

        println!(
            "Alice reversing proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            alice_proving_time,
            alice_verification_time,
            alice_verification_time_rmc,
            alice_affirmation_proof_size
        );
        println!(
            "Bob reversing proving time = {:?}, verification time = {:?}, verification time with RMC = {:?}, proof size = {} bytes",
            bob_proving_time,
            bob_verification_time,
            bob_verification_time_rmc,
            bob_affirmation_proof_size
        );
    }

    #[test]
    fn single_shot_swap() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 2;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<NUM_GENS, L>(b"testing");

        let asset_tree_params = SelRerandParameters {
            even_parameters: account_tree_params.odd_parameters.clone(),
            odd_parameters: account_tree_params.even_parameters.clone(),
        };

        let asset_comm_params = AssetCommitmentParams::new(
            b"asset-comm-params",
            1,
            &asset_tree_params.even_parameters.bp_gens,
        );

        // Setup keys for sender, receiver, and auditor
        let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        // Two different asset-ids for swap
        let asset_id_1 = 1;
        let asset_id_2 = 2;
        let amount_1 = 100;
        let amount_2 = 200;

        let keys = vec![(true, pk_a_e.0)];
        let asset_data_1 = AssetData::new(
            asset_id_1,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();
        let asset_data_2 = AssetData::new(
            asset_id_2,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();

        let set = vec![asset_data_1.commitment, asset_data_2.commitment];
        let asset_tree =
            CurveTree::<L, 1, ark_vesta::VestaConfig, ark_pallas::PallasConfig>::from_leaves(
                &set,
                &asset_tree_params,
                Some(2),
            );
        let asset_path_1 = asset_tree.get_path_to_leaf_for_proof(0, 0);
        let asset_path_2 = asset_tree.get_path_to_leaf_for_proof(1, 0);
        let asset_tree_root = asset_tree.root_node();

        // Create two legs for swap
        let leg_1 = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount_1, asset_id_1).unwrap();
        let (leg_enc_1, leg_enc_rand_1) = leg_1
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();
        let leg_2 = Leg::new(pk_r.0, pk_s.0, keys.clone(), amount_2, asset_id_2).unwrap();
        let (leg_enc_2, leg_enc_rand_2) = leg_2
            .encrypt::<_, Blake2b512>(&mut rng, pk_r_e.0, pk_s_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Alice has accounts for both assets
        let alice_id = PallasFr::rand(&mut rng);
        let (mut alice_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_s.clone(), alice_id);
        alice_account_1.balance = 200;
        let alice_account_comm_1 = alice_account_1.commit(account_comm_key.clone()).unwrap();

        let (mut alice_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_s.clone(), alice_id);
        alice_account_2.balance = 50;
        let alice_account_comm_2 = alice_account_2.commit(account_comm_key.clone()).unwrap();

        // Bob has accounts for both assets
        let bob_id = PallasFr::rand(&mut rng);
        let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_r.clone(), bob_id);
        bob_account_1.balance = 50;
        let bob_account_comm_1 = bob_account_1.commit(account_comm_key.clone()).unwrap();

        let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_r.clone(), bob_id);
        bob_account_2.balance = 300;
        let bob_account_comm_2 = bob_account_2.commit(account_comm_key.clone()).unwrap();

        // Account tree for all four accounts
        let account_comms = vec![
            alice_account_comm_1.0,
            alice_account_comm_2.0,
            bob_account_comm_1.0,
            bob_account_comm_2.0,
        ];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &account_comms,
            &account_tree_params,
            Some(4),
        );
        let account_tree_root = account_tree.root_node();

        // Prepare updated account states for irreversible swap (no counter changes)
        let updated_alice_account_1 = alice_account_1
            .get_state_for_irreversible_send(amount_1)
            .unwrap();
        assert_eq!(
            updated_alice_account_1.balance,
            alice_account_1.balance - amount_1
        );
        assert_eq!(updated_alice_account_1.counter, alice_account_1.counter);
        let updated_alice_account_comm_1 = updated_alice_account_1
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_path_1 = account_tree.get_path_to_leaf_for_proof(0, 0);

        let updated_alice_account_2 = alice_account_2
            .get_state_for_irreversible_receive(amount_2)
            .unwrap();
        assert_eq!(
            updated_alice_account_2.balance,
            alice_account_2.balance + amount_2
        );
        assert_eq!(updated_alice_account_2.counter, alice_account_2.counter);
        let updated_alice_account_comm_2 = updated_alice_account_2
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_path_2 = account_tree.get_path_to_leaf_for_proof(1, 0);

        let updated_bob_account_1 = bob_account_1
            .get_state_for_irreversible_receive(amount_1)
            .unwrap();
        assert_eq!(
            updated_bob_account_1.balance,
            bob_account_1.balance + amount_1
        );
        assert_eq!(updated_bob_account_1.counter, bob_account_1.counter);
        let updated_bob_account_comm_1 = updated_bob_account_1
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_path_1 = account_tree.get_path_to_leaf_for_proof(2, 0);

        let updated_bob_account_2 = bob_account_2
            .get_state_for_irreversible_send(amount_2)
            .unwrap();
        assert_eq!(
            updated_bob_account_2.balance,
            bob_account_2.balance - amount_2
        );
        assert_eq!(updated_bob_account_2.counter, bob_account_2.counter);
        let updated_bob_account_comm_2 = updated_bob_account_2
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_path_2 = account_tree.get_path_to_leaf_for_proof(3, 0);

        let nonce = b"single_shot_swap_nonce_txn_id_1";

        // Combined settlement proofs for both legs
        let even_transcript_settlement = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let odd_transcript_settlement = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut even_prover_settlement = Prover::new(
            &asset_tree_params.even_parameters.pc_gens,
            even_transcript_settlement,
        );
        let mut odd_prover_settlement = Prover::new(
            &asset_tree_params.odd_parameters.pc_gens,
            odd_transcript_settlement,
        );

        let settlement_proof_1 = LegCreationProof::new_with_given_prover(
            &mut rng,
            leg_1.clone(),
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
            asset_path_1.clone(),
            asset_data_1,
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_prover_settlement,
            &mut odd_prover_settlement,
        )
        .unwrap();

        let settlement_proof_2 = LegCreationProof::new_with_given_prover(
            &mut rng,
            leg_2.clone(),
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
            asset_path_2.clone(),
            asset_data_2,
            &asset_tree_root,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
            &mut even_prover_settlement,
            &mut odd_prover_settlement,
        )
        .unwrap();

        let (settlement_even_bp, settlement_odd_bp) = prove_with_rng(
            even_prover_settlement,
            odd_prover_settlement,
            &asset_tree_params,
            &mut rng,
        )
        .unwrap();

        // Combined proofs for Alice (sending in leg1, receiving in leg2)
        let even_transcript_alice = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_alice = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_alice = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_alice,
        );
        let mut odd_prover_alice = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_alice,
        );

        let (alice_sender_proof, alice_sender_nullifier) =
            IrreversibleAffirmAsSenderTxnProof::new_with_given_prover(
                &mut rng,
                amount_1,
                leg_enc_1.clone(),
                leg_enc_rand_1.clone(),
                &alice_account_1,
                &updated_alice_account_1,
                updated_alice_account_comm_1,
                alice_path_1.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        let (alice_receiver_proof, alice_receiver_nullifier) =
            IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover(
                &mut rng,
                amount_2,
                leg_enc_2.clone(),
                leg_enc_rand_2.clone(),
                &alice_account_2,
                &updated_alice_account_2,
                updated_alice_account_comm_2,
                alice_path_2.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_alice,
                &mut odd_prover_alice,
            )
            .unwrap();

        let (alice_even_bp, alice_odd_bp) = prove_with_rng(
            even_prover_alice,
            odd_prover_alice,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();

        // Combined proofs for Bob (receiving in leg1, sending in leg2)
        let even_transcript_bob = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript_bob = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover_bob = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            even_transcript_bob,
        );
        let mut odd_prover_bob = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            odd_transcript_bob,
        );

        let (bob_receiver_proof, bob_receiver_nullifier) =
            IrreversibleAffirmAsReceiverTxnProof::new_with_given_prover(
                &mut rng,
                amount_1,
                leg_enc_1.clone(),
                leg_enc_rand_1.clone(),
                &bob_account_1,
                &updated_bob_account_1,
                updated_bob_account_comm_1,
                bob_path_1.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_bob,
                &mut odd_prover_bob,
            )
            .unwrap();

        let (bob_sender_proof, bob_sender_nullifier) =
            IrreversibleAffirmAsSenderTxnProof::new_with_given_prover(
                &mut rng,
                amount_2,
                leg_enc_2.clone(),
                leg_enc_rand_2.clone(),
                &bob_account_2,
                &updated_bob_account_2,
                updated_bob_account_comm_2,
                bob_path_2.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut even_prover_bob,
                &mut odd_prover_bob,
            )
            .unwrap();

        let (bob_even_bp, bob_odd_bp) = prove_with_rng(
            even_prover_bob,
            odd_prover_bob,
            &account_tree_params,
            &mut rng,
        )
        .unwrap();

        // Verify all proofs
        let clock = Instant::now();

        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut settlement_even_verifier = Verifier::new(transcript_even);
        let mut settlement_odd_verifier = Verifier::new(transcript_odd);

        settlement_proof_1
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_1.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                None,
            )
            .unwrap();

        settlement_proof_2
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_2.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                None,
            )
            .unwrap();

        let (even_tuple_legs, odd_tuple_legs) = get_verification_tuples_with_rng(
            settlement_even_verifier,
            settlement_odd_verifier,
            &settlement_even_bp,
            &settlement_odd_bp,
            &mut rng,
        )
        .unwrap();

        // Verify Alice proofs
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_sender_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_1,
                alice_sender_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        alice_receiver_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_2,
                alice_receiver_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                None,
            )
            .unwrap();

        let (even_tuple_alice, odd_tuple_alice) = get_verification_tuples_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &mut rng,
        )
        .unwrap();

        // Verify Bob proofs
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        bob_receiver_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_1,
                bob_receiver_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        bob_sender_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_2,
                bob_sender_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                None,
            )
            .unwrap();

        let (even_tuple_bob, odd_tuple_bob) = get_verification_tuples_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &mut rng,
        )
        .unwrap();

        let even_tuples = vec![odd_tuple_legs, even_tuple_alice, even_tuple_bob];
        let odd_tuples = vec![even_tuple_legs, odd_tuple_alice, odd_tuple_bob];

        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));
        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));

        let transcript_even = MerlinTranscript::new(LEG_TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(LEG_TXN_ODD_LABEL);
        let mut settlement_even_verifier = Verifier::new(transcript_even);
        let mut settlement_odd_verifier = Verifier::new(transcript_odd);

        settlement_proof_1
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_1.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        settlement_proof_2
            .verify_sigma_protocols_and_enforce_constraints(
                leg_enc_2.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut settlement_even_verifier,
                &mut settlement_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_legs, odd_tuple_legs) = get_verification_tuples_with_rng(
            settlement_even_verifier,
            settlement_odd_verifier,
            &settlement_even_bp,
            &settlement_odd_bp,
            &mut rng,
        )
        .unwrap();

        // Verify Alice proofs
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut alice_even_verifier = Verifier::new(transcript_even);
        let mut alice_odd_verifier = Verifier::new(transcript_odd);

        alice_sender_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_alice_account_comm_1,
                alice_sender_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        alice_receiver_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_alice_account_comm_2,
                alice_receiver_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut alice_even_verifier,
                &mut alice_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_alice, odd_tuple_alice) = get_verification_tuples_with_rng(
            alice_even_verifier,
            alice_odd_verifier,
            &alice_even_bp,
            &alice_odd_bp,
            &mut rng,
        )
        .unwrap();

        // Verify Bob proofs
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut bob_even_verifier = Verifier::new(transcript_even);
        let mut bob_odd_verifier = Verifier::new(transcript_odd);

        bob_receiver_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_1.clone(),
                &account_tree_root,
                updated_bob_account_comm_1,
                bob_receiver_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        bob_sender_proof
            .enforce_constraints_and_verify_only_sigma_protocols(
                leg_enc_2.clone(),
                &account_tree_root,
                updated_bob_account_comm_2,
                bob_sender_nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                &mut bob_even_verifier,
                &mut bob_odd_verifier,
                Some(&mut rmc_0),
            )
            .unwrap();

        let (even_tuple_bob, odd_tuple_bob) = get_verification_tuples_with_rng(
            bob_even_verifier,
            bob_odd_verifier,
            &bob_even_bp,
            &bob_odd_bp,
            &mut rng,
        )
        .unwrap();

        add_verification_tuples_batches_to_rmc(
            vec![odd_tuple_legs, even_tuple_alice, even_tuple_bob],
            vec![even_tuple_legs, odd_tuple_alice, odd_tuple_bob],
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();

        verify_rmc(&rmc_0, &rmc_1).unwrap();

        let verifier_time_rmc = clock.elapsed();

        println!(
            "verifier time {:?}, verifier time (with RandomizedMultChecker) = {:?}",
            verifier_time, verifier_time_rmc
        );
    }

    // Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

    #[cfg(feature = "ignore_prover_input_sanitation")]
    mod input_sanitation_disabled {
        use super::*;

        #[test]
        fn keep_balance_same_in_send_txn() {
            // A sender account sends AffirmAsSenderTxnProof but does not decrease the balance from his account. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 512;
            let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
                setup_gens::<NUM_GENS, L>(b"testing");

            // All parties generate their keys
            let (
                ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
                ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
                ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
            ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

            let asset_id = 1;
            let amount = 100;

            let (_, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Sender account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
            // Assume that account had some balance. Either got it as the issuer or from another transfer
            account.balance = 200;

            let account_tree = get_tree_with_account_comm::<L>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
            )
            .unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0);
            let root = account_tree.root_node();

            let nonce = b"test-nonce";

            // Create an updated account that doesn't decrease the balance
            let mut updated_account = account.get_state_for_send(amount).unwrap();
            updated_account.balance = account.balance; // Keep same balance

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = AffirmAsSenderTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Create an updated account that instead increases the balance
            let mut updated_account = account.get_state_for_send(amount).unwrap();
            updated_account.balance = account.balance + amount; // Increase balance

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = AffirmAsSenderTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );
        }

        #[test]
        fn increase_balance_in_receive_txn() {
            // A receiver account sends AffirmAsReceiverTxnProof but increases the balance. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 512;
            let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
                setup_gens::<NUM_GENS, L>(b"testing");

            // All parties generate their keys
            let (
                ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
                ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
                ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
            ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

            let asset_id = 1;
            let amount = 100;

            let (_, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Receiver account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
            // Assume that account had some balance. Either got it as the issuer or from another transfer
            account.balance = 200;

            let account_tree = get_tree_with_account_comm::<L>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
            )
            .unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0);
            let root = account_tree.root_node();

            let nonce = b"test-nonce";

            // Create a malicious updated account that increases balance
            let mut updated_account = account.get_state_for_receive();
            updated_account.balance = account.balance + amount;

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = AffirmAsReceiverTxnProof::new(
                &mut rng,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );
        }

        #[test]
        fn increase_balance_incorrectly_during_claiming_received_funds() {
            // A receiver account sends ClaimReceivedTxnProof but increases the balance more than the actual claim amount. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 512;
            let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
                setup_gens::<NUM_GENS, L>(b"testing");

            // All parties generate their keys
            let (
                ((_sk_s, pk_s), (_sk_s_e, pk_s_e)),
                ((sk_r, pk_r), (_sk_r_e, pk_r_e)),
                ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
            ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

            let asset_id = 1;
            let amount = 100;

            let (_, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Receiver account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_r, id);
            // Assume that account had some balance and it had sent the receive transaction to increase its counter
            account.balance = 200;
            account.counter += 2;

            let account_tree = get_tree_with_account_comm::<L>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
            )
            .unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0);
            let root = account_tree.root_node();

            let nonce = b"test-nonce";

            // Update account that increases balance more than the actual claim amount
            let mut updated_account = account.get_state_for_claiming_received(amount).unwrap();
            updated_account.balance = account.balance + 75; // Add extra on top of the actual amount

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = ClaimReceivedTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Update account with counter decreased by 1 more than it should be
            let mut updated_account = account.get_state_for_claiming_received(amount).unwrap();
            updated_account.counter -= 1;

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = ClaimReceivedTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );
        }

        #[test]
        fn increase_balance_in_counter_update_by_sender() {
            // A sender account sends SenderCounterUpdateTxnProof but increases their balance when it should remain the same. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 512;
            let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
                setup_gens::<NUM_GENS, L>(b"testing");

            // All parties generate their keys
            let (
                ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
                ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
                ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
            ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

            let asset_id = 1;
            let amount = 100;

            let (_, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Sender account with non-zero counter
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
            account.balance = 50;
            account.counter = 2;

            let account_tree = get_tree_with_account_comm::<L>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
            )
            .unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0);
            let root = account_tree.root_node();

            let nonce = b"test-nonce";

            // Update account that increases balance when it should remain the same
            let mut updated_account = account.get_state_for_decreasing_counter(None).unwrap();
            updated_account.balance = account.balance + amount;

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = SenderCounterUpdateTxnProof::new(
                &mut rng,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Update account with counter decreased by 1 more than it should be
            let mut updated_account = account.get_state_for_decreasing_counter(None).unwrap();
            updated_account.counter -= 1;

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = SenderCounterUpdateTxnProof::new(
                &mut rng,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );
        }

        #[test]
        fn incorrect_updates_in_reverse_send_txn() {
            // A sender account sends SenderReverseTxnProof but makes incorrect updates to balance or counter. These proofs should fail
            let mut rng = rand::thread_rng();

            const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 512;
            let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
                setup_gens::<NUM_GENS, L>(b"testing");

            // All parties generate their keys
            let (
                ((sk_s, pk_s), (_sk_s_e, pk_s_e)),
                ((_sk_r, pk_r), (_sk_r_e, pk_r_e)),
                ((_sk_a, _pk_a), (_sk_a_e, pk_a_e)),
            ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

            let asset_id = 1;
            let amount = 100;

            let (_, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Sender account
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk_s, id);
            // Assume that account had some balance and it had sent the send transaction to increase its counter
            account.balance = 200;
            account.counter += 2;

            let account_tree = get_tree_with_account_comm::<L>(
                &account,
                account_comm_key.clone(),
                &account_tree_params,
            )
            .unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0);
            let root = account_tree.root_node();

            let nonce = b"test-nonce";

            // Update account that increases balance more than required
            let mut updated_account = account.get_state_for_reversing_send(amount).unwrap();
            updated_account.balance = account.balance + 50; // Add extra on top of the actual amount

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = SenderReverseTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Update account with counter decreased by 1 more than it should be
            let mut updated_account = account.get_state_for_reversing_send(amount).unwrap();
            updated_account.counter -= 1;

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let (proof, nullifier) = SenderReverseTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &root,
                        updated_account_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );
        }

        #[test]
        fn incorrect_updates_in_single_shot_settlement() {
            // Test malicious updates in single shot settlement (irreversible send/receive)
            // These proofs should fail because balance or counter updates are incorrect
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 12;
            const L: usize = 512;
            let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
                setup_gens::<NUM_GENS, L>(b"testing");

            let (((sk_s, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), (_, (_, pk_a_e))) =
                setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

            let asset_id = 1;
            let amount = 100;

            let (_, leg_enc, leg_enc_rand) = setup_leg(
                &mut rng,
                pk_s.0,
                pk_r.0,
                pk_a_e.0,
                amount,
                asset_id,
                pk_s_e.0,
                pk_r_e.0,
                enc_key_gen,
                enc_gen,
            );

            // Create sender account
            let sender_id = PallasFr::rand(&mut rng);
            let (mut sender_account, _, _) =
                new_account(&mut rng, asset_id, sk_s.clone(), sender_id);
            sender_account.balance = 200; // Ensure sufficient balance
            sender_account.counter = 5; // Set non-zero counter for testing
            let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

            // Create receiver account
            let receiver_id = PallasFr::rand(&mut rng);
            let (mut receiver_account, _, _) = new_account(&mut rng, asset_id, sk_r, receiver_id);
            receiver_account.balance = 150; // Some initial balance
            receiver_account.counter = 3; // Set non-zero counter for testing
            let receiver_account_comm = receiver_account.commit(account_comm_key.clone()).unwrap();

            // Create the account tree with both accounts
            let account_comms = vec![sender_account_comm.0, receiver_account_comm.0];
            let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
                &account_comms,
                &account_tree_params,
                Some(2),
            );

            let account_tree_root = account_tree.root_node();
            let sender_path = account_tree.get_path_to_leaf_for_proof(0, 0);
            let receiver_path = account_tree.get_path_to_leaf_for_proof(1, 0);

            let nonce = b"test-nonce";

            // Sender trying to decrease balance less than amount
            // Should decrease by 100, but only decreases by 50
            let mut malicious_sender_account = sender_account
                .get_state_for_irreversible_send(amount)
                .unwrap();
            malicious_sender_account.balance += 50;

            let malicious_sender_comm = malicious_sender_account
                .commit(account_comm_key.clone())
                .unwrap();

            let (proof, nullifier) = IrreversibleAffirmAsSenderTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &sender_account,
                &malicious_sender_account,
                malicious_sender_comm,
                sender_path.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &account_tree_root,
                        malicious_sender_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Receiver trying to increase balance more than amount
            // Should increase by 100, but increases by 150
            let mut malicious_receiver_account = receiver_account
                .get_state_for_irreversible_receive(amount)
                .unwrap();
            malicious_receiver_account.balance += 50;

            let malicious_receiver_comm = malicious_receiver_account
                .commit(account_comm_key.clone())
                .unwrap();

            let (proof, nullifier) = IrreversibleAffirmAsReceiverTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &receiver_account,
                &malicious_receiver_account,
                malicious_receiver_comm,
                receiver_path.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &account_tree_root,
                        malicious_receiver_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Sender trying to decrease counter
            let mut malicious_sender_account = sender_account
                .get_state_for_irreversible_send(amount)
                .unwrap();
            malicious_sender_account.counter -= 1;

            let malicious_sender_comm = malicious_sender_account
                .commit(account_comm_key.clone())
                .unwrap();

            let (proof, nullifier) = IrreversibleAffirmAsSenderTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &sender_account,
                &malicious_sender_account,
                malicious_sender_comm,
                sender_path.clone(),
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc.clone(),
                        &account_tree_root,
                        malicious_sender_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );

            // Receiver trying to decrease counter
            let mut malicious_receiver_account = receiver_account
                .get_state_for_irreversible_receive(amount)
                .unwrap();
            malicious_receiver_account.counter -= 1;

            let malicious_receiver_comm = malicious_receiver_account
                .commit(account_comm_key.clone())
                .unwrap();

            let (proof, nullifier) = IrreversibleAffirmAsReceiverTxnProof::new(
                &mut rng,
                amount,
                leg_enc.clone(),
                leg_enc_rand.clone(),
                &receiver_account,
                &malicious_receiver_account,
                malicious_receiver_comm,
                receiver_path,
                &account_tree_root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        &mut rng,
                        leg_enc,
                        &account_tree_root,
                        malicious_receiver_comm,
                        nullifier,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        enc_key_gen,
                        enc_gen,
                        None,
                    )
                    .is_err()
            );
        }

        // More tests can be added like secret key mismatch, incorrect rho or randomness creation, etc.
    }
}
