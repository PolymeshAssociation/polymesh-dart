use ark_std::collections::{BTreeMap, BTreeSet};
// use ark_crypto_primitives::crh::poseidon::TwoToOneCRH;
// use ark_crypto_primitives::crh::TwoToOneCRHScheme;
// use ark_crypto_primitives::sponge::{poseidon::PoseidonConfig, Absorb};
use crate::leg::{LegEncryption, LegEncryptionRandomness};
use crate::poseidon_impls::poseidon_2::{Poseidon_hash_2_simple, Poseidon2Params};
use crate::util::{
    bp_gens_for_vec_commitment,
    enforce_constraints_and_take_challenge_contrib_of_schnorr_t_values_for_common_state_change,
    enforce_constraints_for_randomness_relations,
    generate_schnorr_responses_for_common_state_change,
    generate_schnorr_t_values_for_balance_change,
    generate_schnorr_t_values_for_common_state_change,
    take_challenge_contrib_of_schnorr_t_values_for_balance_change,
    verify_schnorr_for_balance_change, verify_schnorr_for_common_state_change,
};
use crate::util::{
    enforce_balance_change_prover, enforce_balance_change_verifier,
    generate_schnorr_responses_for_balance_change, get_verification_tuples_with_rng,
    initialize_curve_tree_prover, initialize_curve_tree_verifier, prove_with_rng,
    verify_given_verification_tuples, verify_with_rng,
};
use crate::{Error, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::format;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSProof, VerificationTuple, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{
    AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID, NullifierSkGenCounter, PendingTxnCounter,
};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};

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

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
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
        let rho = *p_1.x().unwrap();
        let randomness = *p_2.x().unwrap();
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
        if amount + self.balance > MAX_AMOUNT {
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
        if amount + self.balance > MAX_AMOUNT {
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
        if amount + self.balance > MAX_AMOUNT {
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

// In practice, these will be different for different txns
pub const TXN_ODD_LABEL: &[u8; 13] = b"txn-odd-level";
pub const TXN_EVEN_LABEL: &[u8; 14] = b"txn-even-level";
pub const TXN_CHALLENGE_LABEL: &[u8; 13] = b"txn-challenge";
pub const TXN_INSTANCE_LABEL: &[u8; 18] = b"txn-extra-instance";

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
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokDiscreteLog<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of issuer secret key using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_pk: PokDiscreteLog<Affine<G0>>,
    /// Commitment to the values committed in Bulletproofs
    pub comm_bp: Affine<G0>,
    /// Commitment to randomness for proving knowledge of values committed in Bulletproofs commitment (step 1 of Schnorr)
    pub t_bp: Affine<G0>,
    /// Response for proving knowledge of values committed in Bulletproofs (step 3 of Schnorr)
    pub resp_bp: SchnorrResponse<Affine<G0>>,
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
        ensure_same_accounts(account, updated_account)?;
        if updated_account.balance != account.balance + increase_bal_by {
            return Err(Error::ProofGenerationError(
                "Balance increase incorrect".to_string(),
            ));
        }
        let (mut even_prover, odd_prover, re_randomized_path, rerandomization) =
            initialize_curve_tree_prover(
                rng,
                TXN_EVEN_LABEL,
                TXN_ODD_LABEL,
                leaf_path,
                account_tree_params,
            );

        let mut transcript = even_prover.transcript();

        let mut extra_instance = vec![];
        root.serialize_compressed(&mut extra_instance)?;
        re_randomized_path.serialize_compressed(&mut extra_instance)?;
        nonce.serialize_compressed(&mut extra_instance)?;
        issuer_pk.serialize_compressed(&mut extra_instance)?;
        account.asset_id.serialize_compressed(&mut extra_instance)?;
        increase_bal_by.serialize_compressed(&mut extra_instance)?;
        updated_account_commitment.serialize_compressed(&mut extra_instance)?;
        account_tree_params.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // We don't need to check if the new balance overflows or not as the chain tracks the total supply
        // (total minted value) and ensures that it is bounded, i.e.<= MAX_AMOUNT

        // Need to prove that:
        // 1. id and counter are same in both old and new account commitment
        // 2. nullifier and commitment randomness are correctly formed
        // 3. sk in account commitment is the same as in the issuer's public key
        // 4. New balance = old balance + increase_bal_by

        let id_blinding = F0::rand(rng);
        let counter_blinding = F0::rand(rng);
        let new_balance_blinding = F0::rand(rng);
        let initial_rho_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let new_rho_blinding = F0::rand(rng);
        let old_s_blinding = F0::rand(rng);
        let new_s_blinding = F0::rand(rng);

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
                id_blinding,
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
                id_blinding,
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

        let comm_bp_blinding = F0::rand(rng);
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
        comm_bp.serialize_compressed(&mut transcript)?;

        let prover_challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // TODO: Eliminate duplicate responses
        let resp_leaf = t_r_leaf.response(
            &[
                account.balance.into(),
                account.counter.into(),
                account.rho,
                account.current_rho,
                account.randomness,
                account.id,
                rerandomization,
            ],
            &prover_challenge,
        )?;
        let resp_acc_new = t_acc_new.response(
            &[
                updated_account.balance.into(),
                updated_account.counter.into(),
                updated_account.rho,
                updated_account.current_rho,
                updated_account.randomness,
                updated_account.id,
            ],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_pk = t_pk.gen_proof(&prover_challenge);

        let resp_bp = t_bp.response(
            &[
                comm_bp_blinding,
                updated_account.rho,
                account.current_rho,
                updated_account.current_rho,
                account.randomness,
                updated_account.randomness,
            ],
            &prover_challenge,
        )?;

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
        if self.resp_leaf.len() != NUM_GENERATORS - 1 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS - 1,
                self.resp_leaf.len(),
            ));
        }
        if self.resp_acc_new.len() != (NUM_GENERATORS - 2) {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS - 2,
                self.resp_acc_new.len(),
            ));
        }
        if self.resp_bp.len() != 6 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                6,
                self.resp_bp.len(),
            ));
        }
        let (mut even_verifier, odd_verifier) = initialize_curve_tree_verifier(
            TXN_EVEN_LABEL,
            TXN_ODD_LABEL,
            &self.re_randomized_path,
            root,
            account_tree_params,
        );

        let mut verifier_transcript = even_verifier.transcript();

        let mut extra_instance = vec![];
        root.serialize_compressed(&mut extra_instance)?;
        self.re_randomized_path
            .serialize_compressed(&mut extra_instance)?;
        nonce.serialize_compressed(&mut extra_instance)?;
        issuer_pk.serialize_compressed(&mut extra_instance)?;
        asset_id.serialize_compressed(&mut extra_instance)?;
        increase_bal_by.serialize_compressed(&mut extra_instance)?;
        updated_account_commitment.serialize_compressed(&mut extra_instance)?;
        account_tree_params.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        verifier_transcript
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

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
        self.comm_bp
            .serialize_compressed(&mut verifier_transcript)?;

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let issuer_pk_proj = issuer_pk.into_group();
        let y = self.re_randomized_path.get_rerandomized_leaf() - asset_id_comm - issuer_pk_proj;
        self.resp_leaf.is_valid(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            &y.into_affine(),
            &self.t_r_leaf,
            &verifier_challenge,
        )?;

        let y = updated_account_commitment.0 - asset_id_comm - issuer_pk_proj;
        self.resp_acc_new.is_valid(
            &Self::acc_new_gens(account_comm_key),
            &y.into_affine(),
            &self.t_acc_new,
            &verifier_challenge,
        )?;

        if !self
            .resp_null
            .verify(&nullifier, &nullifier_gen, &verifier_challenge)
        {
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

        self.resp_bp.is_valid(
            &Self::bp_gens_vec(account_tree_params),
            &self.comm_bp,
            &self.t_bp,
            &verifier_challenge,
        )?;

        // counter, rho, id in leaf match the ones in updated account commitment
        if self.resp_leaf.0[1] != self.resp_acc_new.0[1] {
            return Err(Error::ProofVerificationError(
                "Counter mismatch between leaf and new account".to_string(),
            ));
        }
        if self.resp_leaf.0[2] != self.resp_acc_new.0[2] {
            return Err(Error::ProofVerificationError(
                "Initial rho mismatch between leaf and new account".to_string(),
            ));
        }
        if self.resp_leaf.0[5] != self.resp_acc_new.0[5] {
            return Err(Error::ProofVerificationError(
                "ID mismatch between leaf and new account".to_string(),
            ));
        }
        // Balance in leaf is less than the one in the new account commitment by `increase_bal_by`
        if self.resp_leaf.0[0] + (verifier_challenge * F0::from(increase_bal_by))
            != self.resp_acc_new.0[0]
        {
            return Err(Error::ProofVerificationError(
                "Balance increase verification failed".to_string(),
            ));
        }

        // rho matches the one in nullifier
        if self.resp_leaf.0[3] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho mismatch between leaf and nullifier".to_string(),
            ));
        }

        if self.resp_bp.0[1] != self.resp_leaf.0[2] {
            return Err(Error::ProofVerificationError(
                "Initial rho mismatch between the leaf and the one in BP commitment".to_string(),
            ));
        }

        if self.resp_bp.0[2] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Old rho mismatch between the nullifier and the one in BP commitment".to_string(),
            ));
        }

        if self.resp_bp.0[3] != self.resp_acc_new.0[3] {
            return Err(Error::ProofVerificationError(
                "New rho mismatch between the new account commitment and the one in BP commitment"
                    .to_string(),
            ));
        }

        if self.resp_bp.0[4] != self.resp_leaf.0[4] {
            return Err(Error::ProofVerificationError(
                "Old randomness mismatch between the leaf and the one in BP commitment".to_string(),
            ));
        }

        if self.resp_bp.0[5] != self.resp_acc_new.0[4] {
            return Err(Error::ProofVerificationError(
                "New randomness mismatch between the account commitment and the one in BP commitment".to_string(),
            ));
        }

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
    ) -> [Affine<G0>; NUM_GENERATORS - 1] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_comm_key.id_gen(),
            account_tree_params.even_parameters.pc_gens.B_blinding,
        ]
    }

    fn acc_new_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> [Affine<G0>; NUM_GENERATORS - 2] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_comm_key.id_gen(),
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
//          Affirm_s        |         -v           |      1         |
//          Affirm_r        |         0            |      1         |
//          Claim_r         |         +v           |      -1        |
//          CntUpd_s        |         0            |      -1        |
//          Reverse_s       |        +v            |      -1        |
//          Reverse_r       |         0            |      -1        |

/// Proof for variables that change during each account state transition
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonStateChangeProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokDiscreteLog<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of asset-id in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_asset_id: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of secret key of the party's public key in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_pk: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to initial rho, old and current rho, old and current randomness
    pub comm_bp_randomness_relations: Affine<G0>,
    /// Commitment to randomness for proving knowledge of above 5 values (step 1 of Schnorr)
    pub t_bp_randomness_relations: Affine<G0>,
    /// Response for proving knowledge of above 5 values (step 3 of Schnorr)
    pub resp_bp_randomness_relations: SchnorrResponse<Affine<G0>>,
}

/// Proof for variables that change only when the account state transition involves a change in account balance
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProof<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: Affine<G0>,
    pub resp_comm_bp_bal: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_amount: PokPedersenCommitment<Affine<G0>>,
}

pub struct CommonStateChangeProver<
    'a,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_prover: Prover<'a, MerlinTranscript, Affine<G0>>,
    pub odd_prover: Prover<'a, MerlinTranscript, Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    pub leaf_rerandomization: F0,
    pub nullifier: Affine<G0>,
    pub t_r_leaf: SchnorrCommitment<Affine<G0>>,
    pub t_acc_new: SchnorrCommitment<Affine<G0>>,
    pub t_null: PokDiscreteLogProtocol<Affine<G0>>,
    pub t_leg_asset_id: PokPedersenCommitmentProtocol<Affine<G0>>,
    pub t_leg_pk: PokPedersenCommitmentProtocol<Affine<G0>>,
    pub comm_bp_randomness_relations: Affine<G0>,
    pub t_bp_randomness_relations: SchnorrCommitment<Affine<G0>>,
    pub comm_bp_blinding: F0,
    pub r_3: F0,
    pub old_balance_blinding: F0,
    pub new_balance_blinding: F0,
}

pub struct BalanceChangeProver<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub amount: Balance,
    pub old_balance: Balance,
    pub new_balance: Balance,
    pub comm_bp_bal_blinding: G0::ScalarField,
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
    pub even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
    pub odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
    pub prover_is_sender: bool,
    /// Balance can increase, decrease or not change at all
    pub has_balance_decreased: Option<bool>,
    /// Counter can increase or decrease
    pub has_counter_decreased: bool,
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
        ensure_same_accounts(account, updated_account)?;
        if !has_balance_changed {
            // Reconsider: Should I be checking these? Counter can also be checked. So can other fields with a bit more expense
            if account.balance != updated_account.balance {
                return Err(Error::ProofGenerationError(
                    "Balance should be same between old and new account states during receiver affirmation".to_string(),
                ));
            }
        }

        let (mut even_prover, odd_prover, re_randomized_path, leaf_rerandomization) =
            initialize_curve_tree_prover(
                rng,
                TXN_EVEN_LABEL,
                TXN_ODD_LABEL,
                leaf_path,
                account_tree_params,
            );

        let mut extra_instance = vec![];
        root.serialize_compressed(&mut extra_instance)?;
        re_randomized_path.serialize_compressed(&mut extra_instance)?;
        nonce.serialize_compressed(&mut extra_instance)?;
        leg_enc.serialize_compressed(&mut extra_instance)?;
        updated_account_commitment.serialize_compressed(&mut extra_instance)?;
        account_tree_params.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;
        enc_gen.serialize_compressed(&mut extra_instance)?;

        even_prover
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let LegEncryptionRandomness(r_1, r_2, r_3, r_4) = leg_enc_rand;
        let r_pk = if is_sender { r_1 } else { r_2 };

        let id_blinding = F0::rand(rng);
        let sk_blinding = F0::rand(rng);
        let new_counter_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let initial_rho_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let new_rho_blinding = F0::rand(rng);
        let old_randomness_blinding = F0::rand(rng);
        let new_randomness_blinding = F0::rand(rng);

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
        ) = generate_schnorr_t_values_for_common_state_change(
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
            new_counter_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
            asset_id_blinding,
            r_pk,
            r_4,
            &mut even_prover,
            &account_comm_key,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;
        Ok(Self {
            even_prover,
            odd_prover,
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

    pub fn gen_proof<R: CryptoRngCore>(
        self,
        rng: &mut R,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        challenge: &F0,
        account_tree_params: &'a SelRerandParameters<G0, G1>,
    ) -> Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
        let (
            resp_leaf,
            resp_acc_new,
            resp_null,
            resp_leg_asset_id,
            resp_leg_pk,
            resp_bp_randomness_relations,
        ) = generate_schnorr_responses_for_common_state_change(
            account,
            updated_account,
            self.leaf_rerandomization,
            self.comm_bp_blinding,
            &self.t_r_leaf,
            &self.t_acc_new,
            self.t_null,
            self.t_leg_asset_id,
            self.t_leg_pk,
            &self.t_bp_randomness_relations,
            challenge,
        )?;
        let (even_proof, odd_proof) =
            prove_with_rng(self.even_prover, self.odd_prover, &account_tree_params, rng)?;

        Ok(CommonStateChangeProof {
            even_proof,
            odd_proof,
            re_randomized_path: self.re_randomized_path,
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
        old_balance_blinding: F0,
        new_balance_blinding: F0,
        r_3: F0,
        has_balance_decreased: bool,
        mut even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
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

        let amount_blinding = F0::rand(rng);
        let (t_comm_bp_bal, t_leg_amount) = generate_schnorr_t_values_for_balance_change(
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
            self.old_balance,
            self.new_balance,
            self.amount,
            self.comm_bp_bal_blinding,
            self.t_comm_bp_bal,
            self.t_leg_amount,
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
    pub fn init(
        proof: &CommonStateChangeProof<L, F0, F1, G0, G1>,
        leg_enc: &LegEncryption<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        nonce: &[u8],
        prover_is_sender: bool,
        has_balance_decreased: Option<bool>,
        has_counter_decreased: bool,
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        if proof.resp_leaf.len() != (NUM_GENERATORS + 1) {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS + 1,
                proof.resp_leaf.len(),
            ));
        }
        if proof.resp_acc_new.len() != NUM_GENERATORS {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS,
                proof.resp_acc_new.len(),
            ));
        }
        if proof.resp_bp_randomness_relations.len() != 6 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                6,
                proof.resp_bp_randomness_relations.len(),
            ));
        }
        let (mut even_verifier, odd_verifier) = initialize_curve_tree_verifier(
            TXN_EVEN_LABEL,
            TXN_ODD_LABEL,
            &proof.re_randomized_path,
            root,
            account_tree_params,
        );

        let mut extra_instance = vec![];
        root.serialize_compressed(&mut extra_instance)?;
        proof
            .re_randomized_path
            .serialize_compressed(&mut extra_instance)?;
        nonce.serialize_compressed(&mut extra_instance)?;
        leg_enc.serialize_compressed(&mut extra_instance)?;
        updated_account_commitment.serialize_compressed(&mut extra_instance)?;
        account_tree_params.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;
        enc_gen.serialize_compressed(&mut extra_instance)?;

        even_verifier
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        enforce_constraints_and_take_challenge_contrib_of_schnorr_t_values_for_common_state_change(
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
            &mut even_verifier,
            account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        Ok(Self {
            even_verifier,
            odd_verifier,
            prover_is_sender,
            has_balance_decreased,
            has_counter_decreased,
        })
    }

    /// Enforce Bulletproofs constraints for balance change and takes challenge contributions from balance change related subprotocols
    pub fn enforce_constraints_and_take_challenge_contrib_of_balance_change(
        &mut self,
        proof: &BalanceChangeProof<F0, G0>,
        ct_amount: &Affine<G0>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<()> {
        if let Some(has_balance_decreased) = self.has_balance_decreased {
            enforce_balance_change_verifier(
                proof.comm_bp_bal,
                has_balance_decreased,
                &mut self.even_verifier,
            )?;
        } else {
            return Err(Error::ProofVerificationError("`has_balance_decreased` wasn't set but still trying to take challenge contribution".into()));
        }

        let mut verifier_transcript = self.even_verifier.transcript();

        take_challenge_contrib_of_schnorr_t_values_for_balance_change(
            ct_amount,
            &proof.t_comm_bp_bal,
            &proof.resp_leg_amount,
            enc_key_gen,
            enc_gen,
            &mut verifier_transcript,
        )?;

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
    ) -> Result<()> {
        let (even_tuple, odd_tuple) = self.verify_except_bp(
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
        )?;

        verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params)
    }

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_except_bp<R: CryptoRngCore>(
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
        rng: &mut R,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let pc_gens = &account_tree_params.even_parameters.pc_gens;
        let bp_gens = &account_tree_params.even_parameters.bp_gens;

        verify_schnorr_for_common_state_change(
            leg_enc,
            self.prover_is_sender,
            self.has_counter_decreased,
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
        )?;

        if let Some(balance_change_proof) = balance_change_proof {
            verify_schnorr_for_balance_change(
                &leg_enc,
                &balance_change_proof.resp_leg_amount,
                &balance_change_proof.comm_bp_bal,
                &balance_change_proof.t_comm_bp_bal,
                &balance_change_proof.resp_comm_bp_bal,
                &challenge,
                pc_gens,
                bp_gens,
                enc_key_gen,
                enc_gen,
            )?;

            // Balance in leaf (old account) is same as in the old balance commitment
            if common_state_change_proof.resp_leaf.0[1]
                != balance_change_proof.resp_comm_bp_bal.0[2]
            {
                return Err(Error::ProofVerificationError(
                    "Balance in leaf does not match old balance commitment".to_string(),
                ));
            }

            // Balance in new account commitment is same as in the new balance commitment
            if common_state_change_proof.resp_acc_new.0[1]
                != balance_change_proof.resp_comm_bp_bal.0[3]
            {
                return Err(Error::ProofVerificationError(
                    "Balance in new account does not match new balance commitment".to_string(),
                ));
            }

            // Amount in leg is same as amount in commitment
            if balance_change_proof.resp_leg_amount.response2
                != balance_change_proof.resp_comm_bp_bal.0[1]
            {
                return Err(Error::ProofVerificationError(
                    "Amount in leg does not match amount commitment".to_string(),
                ));
            }
        } else {
            // Balance in leaf (old account) is same as in the new account commitment
            if common_state_change_proof.resp_leaf.0[1]
                != common_state_change_proof.resp_acc_new.0[1]
            {
                return Err(Error::ProofVerificationError(
                    "Balance in leaf does not match the new account commitment".to_string(),
                ));
            }
        }

        get_verification_tuples_with_rng(
            self.even_verifier,
            self.odd_verifier,
            &common_state_change_proof.even_proof,
            &common_state_change_proof.odd_proof,
            rng,
        )
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

        let mut common_prover = CommonStateChangeProver::init(
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
            &mut common_prover.even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = common_prover
            .even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof = common_prover.gen_proof(
            rng,
            account,
            updated_account,
            &challenge,
            account_tree_params,
        )?;

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
    ) -> Result<()> {
        let (even_tuple, odd_tuple) = self.verify_except_bp(
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            rng,
        )?;

        verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params)
    }

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_except_bp<R: CryptoRngCore>(
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
            false,
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
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_except_bp(
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
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. new counter - old counter = 1
        // 5. initial rho is same in both old and new commitments
        // 6. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 7. randomness in new account commitment is square of randomness in old account commitment
        // 8. pk in leg has the sk in account commitment

        let mut common_prover = CommonStateChangeProver::init(
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
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = common_prover
            .even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof = common_prover.gen_proof(
            rng,
            account,
            updated_account,
            &challenge,
            account_tree_params,
        )?;

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
    ) -> Result<()> {
        let (even_tuple, odd_tuple) = self.verify_except_bp(
            leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
            rng,
        )?;

        verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params)
    }

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_except_bp<R: CryptoRngCore>(
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
            false,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify_except_bp(
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

        let mut common_prover = CommonStateChangeProver::init(
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
            &mut common_prover.even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = common_prover
            .even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof = common_prover.gen_proof(
            rng,
            account,
            updated_account,
            &challenge,
            account_tree_params,
        )?;

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
    ) -> Result<()> {
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
            true,
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
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify(
            rng,
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
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. old counter - new counter = 1
        // 5. initial rho is same in both old and new commitments
        // 6. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 7. randomness in new account commitment is square of randomness in old account commitment
        // 8. pk in leg has the sk in account commitment

        let mut common_prover = CommonStateChangeProver::init(
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
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = common_prover
            .even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof = common_prover.gen_proof(
            rng,
            account,
            updated_account,
            &challenge,
            account_tree_params,
        )?;

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
    ) -> Result<()> {
        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            true,
            None,
            true,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify(
            rng,
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

        let mut common_prover = CommonStateChangeProver::init(
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
            &mut common_prover.even_prover,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
            enc_key_gen,
            enc_gen,
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = common_prover
            .even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof = common_prover.gen_proof(
            rng,
            account,
            updated_account,
            &challenge,
            account_tree_params,
        )?;

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
    ) -> Result<()> {
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
            true,
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
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify(
            rng,
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
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. old counter - new counter = 1
        // 5. initial rho is same in both old and new commitments
        // 6. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 7. randomness in new account commitment is square of randomness in old account commitment
        // 8. pk in leg has the sk in account commitment

        let mut common_prover = CommonStateChangeProver::init(
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
        )?;

        let nullifier = common_prover.nullifier;

        let challenge = common_prover
            .even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let common_proof = common_prover.gen_proof(
            rng,
            account,
            updated_account,
            &challenge,
            account_tree_params,
        )?;

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
    ) -> Result<()> {
        let mut verifier = StateChangeVerifier::init(
            &self.common_proof,
            &leg_enc,
            root,
            updated_account_commitment,
            nullifier,
            nonce,
            false,
            None,
            true,
            account_tree_params,
            &account_comm_key,
            enc_key_gen,
            enc_gen,
        )?;

        let challenge = verifier
            .even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        verifier.verify(
            rng,
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
        )
    }
}

/// This is the proof for doing proof of balance with an auditor. This reveals the ID for proof efficiency as the public key is already revealed.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PobWithAuditorProof<G: AffineRepr> {
    pub nullifier: G,
    pub t_acc: G,
    pub resp_acc: SchnorrResponse<G>,
    pub resp_null: PokDiscreteLog<G>,
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
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. nullifier is created from current_rho
        //
        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        let mut prover_transcript = MerlinTranscript::new(TXN_POB_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        account.id.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        prover_transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

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

        t_acc.challenge_contribution(&mut prover_transcript)?;
        t_null.challenge_contribution(&null_gen, &nullifier, &mut prover_transcript)?;
        t_pk.challenge_contribution(&pk_gen, &pk, &mut prover_transcript)?;

        let prover_challenge =
            prover_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let resp_acc = t_acc.response(
            &[account.rho, account.current_rho, account.randomness],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_proof(&prover_challenge);
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
        let mut verifier_transcript = MerlinTranscript::new(TXN_POB_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        id.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        verifier_transcript
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.t_acc.serialize_compressed(&mut verifier_transcript)?;
        self.resp_null.challenge_contribution(
            &null_gen,
            &self.nullifier,
            &mut verifier_transcript,
        )?;
        self.resp_pk
            .challenge_contribution(&pk_gen, &pk, &mut verifier_transcript)?;

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

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
        if !self
            .resp_null
            .verify(&self.nullifier, &null_gen, &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "Nullifier proof verification failed".to_string(),
            ));
        }
        if !self.resp_pk.verify(&pk, &pk_gen, &verifier_challenge) {
            return Err(Error::ProofVerificationError(
                "Public key proof verification failed".to_string(),
            ));
        }

        // rho matches the one in nullifier
        if self.resp_acc.0[1] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho in account does not match the one in nullifier".to_string(),
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
    pub resp_null: PokDiscreteLog<G>,
    pub resp_pk: PokDiscreteLog<G>,
    /// For proving correctness of twisted Elgamal ciphertext of asset-id in each leg
    pub resp_asset_id: Vec<PokDiscreteLog<G>>,
    /// For proving correctness of twisted Elgamal ciphertext of sender public key. Used when prover is sender.
    pub resp_pk_send: BTreeMap<usize, PokDiscreteLog<G>>,
    /// For proving correctness of twisted Elgamal ciphertext of receiver public key. Used when prover is receiver.
    pub resp_pk_recv: BTreeMap<usize, PokDiscreteLog<G>>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is receiver. `\sum{v}` is the total received amount in the legs
    pub resp_recv_amount: PokDiscreteLog<G>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is sender. `\sum{v}` is the total sent amount in the legs
    pub resp_sent_amount: PokDiscreteLog<G>,
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

        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        let at = G::ScalarField::from(account.asset_id);
        let h_at = enc_gen * at;

        let mut prover_transcript = MerlinTranscript::new(TXN_POB_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pending_sent_amount.serialize_compressed(&mut extra_instance)?;
        pending_recv_amount.serialize_compressed(&mut extra_instance)?;
        account.asset_id.serialize_compressed(&mut extra_instance)?;
        account.balance.serialize_compressed(&mut extra_instance)?;
        account.counter.serialize_compressed(&mut extra_instance)?;
        h_at.serialize_compressed(&mut extra_instance)?;
        for l in &legs {
            l.0.serialize_compressed(&mut extra_instance)?;
        }
        account.id.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;
        enc_gen.serialize_compressed(&mut extra_instance)?;

        prover_transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarField::rand(rng);
        let current_rho_blinding = G::ScalarField::rand(rng);

        // For proving correctness of twisted Elgamal ciphertext of asset-id
        let mut t_asset_id = vec![];

        // For proving correctness of twisted Elgamal ciphertext of sender public key. Used when prover is sender.
        let mut t_pk_send = BTreeMap::new();
        // For proving correctness of twisted Elgamal ciphertext of receiver public key. Used when prover is receiver.
        let mut t_pk_recv = BTreeMap::new();

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

        // Sum of all C_v where prover is sender
        let mut enc_total_send = G::Group::zero();
        // Sum of all C_v where prover is receiver
        let mut enc_total_recv = G::Group::zero();

        // TODO: These protocols can be aggregated together with an RLC. Oe even the batch-Sigma protocol can be used.
        for i in 0..num_pending_txns {
            let LegEncryptionRandomness(r_1, r_2, r_3, r_4) = legs[i].1;

            if receiver_in_leg_indices.contains(&i) {
                // Proving knowledge of r_2 in C_r - pk = g * r_2
                let t_leg_pk =
                    PokDiscreteLogProtocol::init(r_2, G::ScalarField::rand(rng), &enc_key_gen);
                t_pk_recv.insert(i, t_leg_pk);
                sum_r_3_recv += r_3;
                enc_total_recv += legs[i].0.ct_amount;
            } else if sender_in_leg_indices.contains(&i) {
                // Proving knowledge of r_1 in C_s - pk = g * r_1
                let t_leg_pk =
                    PokDiscreteLogProtocol::init(r_1, G::ScalarField::rand(rng), &enc_key_gen);
                t_pk_send.insert(i, t_leg_pk);
                sum_r_3_sent += r_3;
                enc_total_send += legs[i].0.ct_amount;
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            // Proving knowledge of r_4 in C_at - h * at = g * r_4
            let t_leg_asset_id =
                PokDiscreteLogProtocol::init(r_4, G::ScalarField::rand(rng), &enc_key_gen);
            t_asset_id.push(t_leg_asset_id);
        }

        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is sender. \sum{v} is the total sent amount in the legs
        let t_sent_amount =
            PokDiscreteLogProtocol::init(sum_r_3_sent, G::ScalarField::rand(rng), &enc_key_gen);
        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is receiver. \sum{v} is the total received amount in the legs
        let t_recv_amount =
            PokDiscreteLogProtocol::init(sum_r_3_recv, G::ScalarField::rand(rng), &enc_key_gen);

        t_acc.challenge_contribution(&mut prover_transcript)?;
        t_null.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &nullifier,
            &mut prover_transcript,
        )?;
        t_pk.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut prover_transcript)?;

        let pk = pk.into_group();

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let y = legs[i].0.ct_r.into_group() - pk;
                t_pk_recv[&i].challenge_contribution(
                    &enc_key_gen,
                    &y.into_affine(),
                    &mut prover_transcript,
                )?;
            } else if sender_in_leg_indices.contains(&i) {
                let y = legs[i].0.ct_s.into_group() - pk;
                t_pk_send[&i].challenge_contribution(
                    &enc_key_gen,
                    &y.into_affine(),
                    &mut prover_transcript,
                )?;
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = legs[i].0.ct_asset_id.into_group() - h_at;
            t_asset_id[i].challenge_contribution(
                &enc_key_gen,
                &y.into_affine(),
                &mut prover_transcript,
            )?;
        }

        let y = enc_total_send - (enc_gen * G::ScalarField::from(pending_sent_amount));
        t_sent_amount.challenge_contribution(
            &enc_key_gen,
            &y.into_affine(),
            &mut prover_transcript,
        )?;
        let y = enc_total_recv - (enc_gen * G::ScalarField::from(pending_recv_amount));
        t_recv_amount.challenge_contribution(
            &enc_key_gen,
            &y.into_affine(),
            &mut prover_transcript,
        )?;

        let prover_challenge =
            prover_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut resp_pk_send = BTreeMap::new();
        let mut resp_pk_recv = BTreeMap::new();
        let mut resp_asset_id = vec![];

        // TODO: Eliminate duplicate responses
        let resp_acc = t_acc.response(
            &[account.rho, account.current_rho, account.randomness],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_pk = t_pk.gen_proof(&prover_challenge);

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                resp_pk_recv.insert(i, t_pk_recv[&i].clone().gen_proof(&prover_challenge));
            } else if sender_in_leg_indices.contains(&i) {
                resp_pk_send.insert(i, t_pk_send[&i].clone().gen_proof(&prover_challenge));
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }
            resp_asset_id.push(t_asset_id[i].clone().gen_proof(&prover_challenge));
        }

        let resp_sent_amount = t_sent_amount.gen_proof(&prover_challenge);
        let resp_recv_amount = t_recv_amount.gen_proof(&prover_challenge);

        Ok(Self {
            nullifier,
            t_acc: t_acc.t,
            resp_acc,
            resp_null,
            resp_pk,
            resp_asset_id,
            resp_pk_recv,
            resp_pk_send,
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
        if legs.len() != self.resp_asset_id.len() {
            return Err(Error::ProofVerificationError(
                "Legs and asset ID responses length mismatch".to_string(),
            ));
        }
        if sender_in_leg_indices.len() != self.resp_pk_send.len() {
            return Err(Error::ProofVerificationError(
                "Sender indices and responses length mismatch".to_string(),
            ));
        }
        if receiver_in_leg_indices.len() != self.resp_pk_recv.len() {
            return Err(Error::ProofVerificationError(
                "Receiver indices and responses length mismatch".to_string(),
            ));
        }

        let num_pending_txns = legs.len();

        let mut verifier_transcript = MerlinTranscript::new(TXN_POB_LABEL);

        let at = G::ScalarField::from(asset_id);
        let h_at = enc_gen * at;

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pending_sent_amount.serialize_compressed(&mut extra_instance)?;
        pending_recv_amount.serialize_compressed(&mut extra_instance)?;
        asset_id.serialize_compressed(&mut extra_instance)?;
        balance.serialize_compressed(&mut extra_instance)?;
        counter.serialize_compressed(&mut extra_instance)?;
        h_at.serialize_compressed(&mut extra_instance)?;
        for l in &legs {
            l.serialize_compressed(&mut extra_instance)?;
        }
        id.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;
        enc_gen.serialize_compressed(&mut extra_instance)?;

        verifier_transcript
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        self.t_acc.serialize_compressed(&mut verifier_transcript)?;
        self.resp_null.challenge_contribution(
            &account_comm_key.current_rho_gen(),
            &self.nullifier,
            &mut verifier_transcript,
        )?;
        self.resp_pk.challenge_contribution(
            &account_comm_key.sk_gen(),
            pk,
            &mut verifier_transcript,
        )?;

        let mut enc_total_send = G::Group::zero();
        let mut enc_total_recv = G::Group::zero();
        let mut pk_recv_y = BTreeMap::new();
        let mut pk_send_y = BTreeMap::new();

        let pk_g = pk.into_group();
        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_r.into_group() - pk_g).into_affine();
                let resp = self
                    .resp_pk_recv
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk recv: {i}")))?;
                resp.challenge_contribution(&enc_key_gen, &y, &mut verifier_transcript)?;
                enc_total_recv += legs[i].ct_amount;
                pk_recv_y.insert(i, y);
            } else if sender_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_s.into_group() - pk_g).into_affine();
                let resp = self
                    .resp_pk_send
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk send: {i}")))?;
                resp.challenge_contribution(&enc_key_gen, &y, &mut verifier_transcript)?;
                enc_total_send += legs[i].ct_amount;
                pk_send_y.insert(i, y);
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = legs[i].ct_asset_id.into_group() - h_at;
            self.resp_asset_id[i].challenge_contribution(
                &enc_key_gen,
                &y.into_affine(),
                &mut verifier_transcript,
            )?;
        }

        let y_total_send =
            (enc_total_send - (enc_gen * G::ScalarField::from(pending_sent_amount))).into_affine();
        self.resp_sent_amount.challenge_contribution(
            &enc_key_gen,
            &y_total_send,
            &mut verifier_transcript,
        )?;
        let y_total_recv =
            (enc_total_recv - (enc_gen * G::ScalarField::from(pending_recv_amount))).into_affine();
        self.resp_recv_amount.challenge_contribution(
            &enc_key_gen,
            &y_total_recv,
            &mut verifier_transcript,
        )?;

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

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
        if !self.resp_null.verify(
            &self.nullifier,
            &account_comm_key.current_rho_gen(),
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ));
        }
        if !self
            .resp_pk
            .verify(&pk, &account_comm_key.sk_gen(), &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "Public key verification failed".to_string(),
            ));
        }

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let comm = self
                    .resp_pk_recv
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk recv: {i}")))?;
                if !comm.verify(
                    &pk_recv_y.remove(&i).unwrap(),
                    &enc_key_gen,
                    &verifier_challenge,
                ) {
                    return Err(Error::ProofVerificationError(format!(
                        "Receiver public key verification failed for leg {}",
                        i
                    )));
                }
            } else if sender_in_leg_indices.contains(&i) {
                let comm = self
                    .resp_pk_send
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk send: {i}")))?;
                if !comm.verify(
                    &pk_send_y.remove(&i).unwrap(),
                    &enc_key_gen,
                    &verifier_challenge,
                ) {
                    return Err(Error::ProofVerificationError(format!(
                        "Sender public key verification failed for leg {}",
                        i
                    )));
                }
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = legs[i].ct_asset_id.into_group() - h_at;
            if !self.resp_asset_id[i].verify(&y.into_affine(), &enc_key_gen, &verifier_challenge) {
                return Err(Error::ProofVerificationError(format!(
                    "Asset ID verification failed for leg {}",
                    i
                )));
            }
        }

        if !self
            .resp_sent_amount
            .verify(&y_total_send, &enc_key_gen, &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "resp_sent_amount verification failed".to_string(),
            ));
        }

        if !self
            .resp_recv_amount
            .verify(&y_total_recv, &enc_key_gen, &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "resp_recv_amount verification failed".to_string(),
            ));
        }

        // rho matches the one in nullifier
        if self.resp_acc.0[1] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho mismatch between account and nullifier".to_string(),
            ));
        }

        Ok(())
    }
}

fn ensure_same_accounts<G: AffineRepr>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
) -> Result<()> {
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

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account_registration::tests::{new_account, setup_comm_key};
    use crate::keys::keygen_sig;
    use crate::leg::{AssetCommitmentParams, AssetData, Leg, SettlementTxnProof};
    use crate::leg::tests::setup_keys;
    use crate::util::batch_verify_bp;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;

    type Fr = ark_pallas::Fr;

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
        LegEncryptionRandomness<Fr>,
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

    pub fn setup_gens<R: CryptoRngCore, const NUM_GENS: usize, const L: usize>(
        rng: &mut R,
    ) -> (
        SelRerandParameters<PallasParameters, VestaParameters>,
        impl AccountCommitmentKeyTrait<PallasA> + use<R, NUM_GENS, L>,
        PallasA,
        PallasA,
    ) {
        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS)
                .unwrap();
        let account_comm_key = setup_comm_key::<R, PallasA>(rng);
        let enc_key_gen = PallasA::rand(rng);
        let enc_gen = PallasA::rand(rng);
        (account_tree_params, account_comm_key, enc_key_gen, enc_gen)
    }

    #[test]
    fn increase_supply_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, _, _) = setup_gens::<_, NUM_GENS, L>(&mut rng);

        let asset_id = 1;

        // Issuer creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let id = Fr::rand(&mut rng);
        let (account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk_i, id);

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
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk_s, id);
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
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn receive_txn() {
        let mut rng = rand::thread_rng();

        // Setup beings

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk_r, id);
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
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
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
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk_r, id);
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
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn counter_update_txn_by_sender() {
        // This is similar to receive txn as only account's counter is decreased, balance remains same.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk_s, id);
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
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn reverse_send_txn() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk_s, id);
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
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn reverse_receive_txn() {
        // This is similar to receive txn as only account's counter is decreased, balance remains same.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk_r, id);
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
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &account_tree_params,
                account_comm_key,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        log::info!("total proof size = {}", proof.compressed_size());
        log::info!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }

    #[test]
    fn pob_with_auditor_as_verifier() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

        let asset_id = 1;

        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        // Account exists with some balance and pending txns
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk, id.clone());
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

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

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
        let id = Fr::rand(&mut rng);
        let (mut account, _, _) = new_account::<_, PallasA>(&mut rng, asset_id, sk, id.clone());
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
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
            let id = Fr::rand(&mut rng);
            let (mut account, _, _) =
                new_account::<_, PallasA>(&mut rng, asset_id, sk_s.clone(), id);
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
                .verify_except_bp(
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
    }

    #[test]
    fn batch_receive_txn_proofs() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 1024;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<_, NUM_GENS, L>(&mut rng);

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
            let id = Fr::rand(&mut rng);
            let (mut account, _, _) =
                new_account::<_, PallasA>(&mut rng, asset_id, sk_r.clone(), id);
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
                .verify_except_bp(
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
    }

    #[test]
    fn single_shot_settlement() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 1024;
        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens::<_, NUM_GENS, L>(&mut rng);

        let (
            ((sk_s, pk_s), (_, pk_s_e)),
            ((sk_r, pk_r), (_, pk_r_e)),
            (_, (_, pk_a_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let asset_tree_params =
            SelRerandParameters::<
                ark_vesta::VestaConfig,
                ark_pallas::PallasConfig,
            >::new(NUM_GENS, NUM_GENS)
            .unwrap();

        // Create asset commitment parameters
        let asset_comm_params = AssetCommitmentParams::new::<Blake2b512>(
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
        let asset_tree = curve_tree_relations::curve_tree::CurveTree::<
            L,
            1,
            ark_vesta::VestaConfig,
            ark_pallas::PallasConfig,
        >::from_leaves(&set, &asset_tree_params, Some(1));

        // Get asset tree path
        let asset_path = asset_tree.get_path_to_leaf_for_proof(0, 0);
        let asset_tree_root = asset_tree.root_node();

        // Create a single leg
        let leg = Leg::new(pk_s.0, pk_r.0, keys.clone(), amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(&mut rng, pk_s_e.0, pk_r_e.0, enc_key_gen, enc_gen)
            .unwrap();

        // Create sender account
        let sender_id = Fr::rand(&mut rng);
        let (mut sender_account, _, _) =
            new_account::<_, PallasA>(&mut rng, asset_id, sk_s, sender_id);
        sender_account.balance = 200; // Ensure sufficient balance
        let sender_account_comm = sender_account.commit(account_comm_key.clone()).unwrap();

        // Create receiver account
        let receiver_id = Fr::rand(&mut rng);
        let (mut receiver_account, _, _) =
            new_account::<_, PallasA>(&mut rng, asset_id, sk_r, receiver_id);
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
        let updated_sender_account = sender_account.get_state_for_send(amount).unwrap();
        let updated_sender_account_comm = updated_sender_account
            .commit(account_comm_key.clone())
            .unwrap();
        let sender_path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let updated_receiver_account = receiver_account.get_state_for_receive();
        let updated_receiver_account_comm = updated_receiver_account
            .commit(account_comm_key.clone())
            .unwrap();
        let receiver_path = account_tree.get_path_to_leaf_for_proof(1, 0);

        let nonce = b"single_shot_settlement_nonce_txn_id_1";

        // Create all three proofs
        let settlement_proof = SettlementTxnProof::new(
            &mut rng,
            leg.clone(),
            leg_enc.clone(),
            leg_enc_rand.clone(),
            asset_path.clone(),
            asset_data,
            nonce,
            &asset_tree_params,
            &asset_comm_params,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let (sender_proof, sender_nullifier) = AffirmAsSenderTxnProof::new(
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

        let (receiver_proof, receiver_nullifier) = AffirmAsReceiverTxnProof::new(
            &mut rng,
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

        // All 3 can be verified in parallel
        let (settlement_even, settlement_odd) = settlement_proof
            .verify_except_bp(
                leg_enc.clone(),
                &asset_tree_root,
                nonce,
                &asset_tree_params,
                &asset_comm_params,
                enc_key_gen,
                enc_gen,
                &mut rng,
            )
            .unwrap();

        let (sender_even, sender_odd) = sender_proof
            .verify_except_bp(
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
            )
            .unwrap();

        let (receiver_even, receiver_odd) = receiver_proof
            .verify_except_bp(
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
            )
            .unwrap();

        // Asset tree uses opposite curves than account tree so merging accordingly
        let even_tuples = vec![settlement_odd, sender_even, receiver_even];
        let odd_tuples = vec![settlement_even, sender_odd, receiver_odd];

        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();
    }
}
