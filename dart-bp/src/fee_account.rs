use crate::account::{
    AccountCommitmentKeyTrait, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_INSTANCE_LABEL,
    TXN_ODD_LABEL,
};
use crate::error::*;
use crate::util::{
    initialize_curve_tree_prover, initialize_curve_tree_verifier, prove_with_rng, verify_with_rng,
};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::string::ToString;
use ark_std::{UniformRand, vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance, FEE_AMOUNT_BITS, MAX_FEE_AMOUNT};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};

/// To commit, use the same commitment key as non-fee asset account commitment.
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeeAccountState<G: AffineRepr> {
    // TODO: Remove this later.
    pub sk: G::ScalarField,
    pub balance: Balance,
    /// This is 0 for PolyX is always revealed when paying fee
    /// Including the asset-id as we might need to support multiple fee currencies in future.
    pub asset_id: AssetId,
    pub rho: G::ScalarField,
    pub randomness: G::ScalarField,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeeAccountStateCommitment<G: AffineRepr>(pub G);

impl<G: AffineRepr> FeeAccountState<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        balance: Balance,
        asset_id: AssetId,
    ) -> Result<Self> {
        let rho = G::ScalarField::rand(rng);
        let randomness = G::ScalarField::rand(rng);

        Ok(Self {
            sk,
            balance,
            asset_id,
            rho,
            randomness,
        })
    }

    pub fn commit(
        &self,
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<FeeAccountStateCommitment<G>> {
        let comm = G::Group::msm(
            &[
                account_comm_key.sk_gen(),
                account_comm_key.balance_gen(),
                account_comm_key.asset_id_gen(),
                account_comm_key.rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            &[
                self.sk,
                G::ScalarField::from(self.balance),
                G::ScalarField::from(self.asset_id),
                self.rho,
                self.randomness,
            ],
        )
        .map_err(Error::size_mismatch)?;
        Ok(FeeAccountStateCommitment(comm.into_affine()))
    }

    pub fn get_state_for_topup<R: CryptoRngCore>(&self, rng: &mut R, amount: u64) -> Result<Self> {
        if amount + self.balance > MAX_FEE_AMOUNT {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.refresh_randomness_for_state_change(rng);
        Ok(new_state)
    }

    pub fn get_state_for_payment<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        fee_amount: u64,
    ) -> Result<Self> {
        if fee_amount > self.balance {
            return Err(Error::AmountTooLarge(fee_amount));
        }
        let mut new_state = self.clone();
        new_state.balance -= fee_amount;
        new_state.refresh_randomness_for_state_change(rng);
        Ok(new_state)
    }

    pub fn refresh_randomness_for_state_change<R: CryptoRngCore>(&mut self, rng: &mut R) {
        self.rho = G::ScalarField::rand(rng);
        self.randomness = G::ScalarField::rand(rng);
    }

    pub fn nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        (comm_key.rho_gen() * self.rho).into()
    }
}

const FEE_REG_TXN_LABEL: &'static [u8; 24] = b"fee_account_registration";

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RegTxnProof<G: AffineRepr> {
    pub resp_acc_comm: PokPedersenCommitment<G>,
    pub resp_pk: PokDiscreteLog<G>,
}

impl<G: AffineRepr> RegTxnProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: G,
        account: &FeeAccountState<G>,
        account_commitment: FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        account.asset_id.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // D = pk + g_balance * balance + g_asset_id * asset_id
        let D = pk.into_group()
            + (account_comm_key.balance_gen() * G::ScalarField::from(account.balance))
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(account.asset_id));

        let sk_blinding = G::ScalarField::rand(rng);
        let rho_blinding = G::ScalarField::rand(rng);
        let randomness_blinding = G::ScalarField::rand(rng);

        // For proving Comm - D = g_rho * rho + g_randomness * randomness
        let comm_protocol = PokPedersenCommitmentProtocol::init(
            account.rho,
            rho_blinding,
            &account_comm_key.rho_gen(),
            account.randomness,
            randomness_blinding,
            &account_comm_key.randomness_gen(),
        );
        let reduced_acc_comm = (account_commitment.0.into_group() - D).into_affine();
        comm_protocol.challenge_contribution(
            &account_comm_key.rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;

        let pk_protocol =
            PokDiscreteLogProtocol::init(account.sk, sk_blinding, &account_comm_key.sk_gen());
        pk_protocol.challenge_contribution(&account_comm_key.sk_gen(), &pk, &mut transcript)?;

        let prover_challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let resp_acc_comm = comm_protocol.gen_proof(&prover_challenge);
        let resp_pk = pk_protocol.gen_proof(&prover_challenge);

        Ok(Self {
            resp_acc_comm,
            resp_pk,
        })
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        _rng: &mut R,
        pk: &G,
        balance: Balance,
        asset_id: AssetId,
        account_commitment: &FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        asset_id.serialize_compressed(&mut extra_instance)?;
        account_commitment.serialize_compressed(&mut extra_instance)?;
        pk.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // D = pk + g_balance * balance + g_asset_id * asset_id
        let D = pk.into_group()
            + (account_comm_key.balance_gen() * G::ScalarField::from(balance))
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id));

        let reduced_acc_comm = (account_commitment.0.into_group() - D).into_affine();
        self.resp_acc_comm.challenge_contribution(
            &account_comm_key.rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;

        self.resp_pk
            .challenge_contribution(&account_comm_key.sk_gen(), pk, &mut transcript)?;

        let verifier_challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        if !self.resp_acc_comm.verify(
            &reduced_acc_comm,
            &account_comm_key.rho_gen(),
            &account_comm_key.randomness_gen(),
            &verifier_challenge,
        ) {
            return Err(Error::ProofVerificationError(
                "Account commitment proof verification failed".to_string(),
            ));
        }

        if !self
            .resp_pk
            .verify(pk, &account_comm_key.sk_gen(), &verifier_challenge)
        {
            return Err(Error::ProofVerificationError(
                "Public key proof verification failed".to_string(),
            ));
        }

        Ok(())
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeeAccountTopupTxnProof<
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
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeeAccountTopupTxnProof<L, F0, F1, G0, G1>
{
    /// `issuer_pk` is the public key of the investor who is topping up his fee account
    /// and has the same secret key as the one in `account`
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        issuer_pk: Affine<G0>,
        increase_bal_by: Balance,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Ensure accounts are consistent (same sk, asset_id)
        if account.sk != updated_account.sk {
            return Err(Error::ProofGenerationError(
                "Secret key mismatch between old and new account states".to_string(),
            ));
        }
        if account.asset_id != updated_account.asset_id {
            return Err(Error::ProofGenerationError(
                "Asset ID mismatch between old and new account states".to_string(),
            ));
        }
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
        // 1. nullifier is correctly formed
        // 2. sk in account commitment is the same as in the issuer's public key
        // 3. New balance = old balance + increase_bal_by

        let new_balance_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let new_rho_blinding = F0::rand(rng);
        let old_s_blinding = F0::rand(rng);
        let new_s_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.rho_gen();
        let pk_gen = account_comm_key.sk_gen();
        let nullifier = account.nullifier(&account_comm_key);

        // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
        let t_r_leaf = SchnorrCommitment::new(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            vec![
                new_balance_blinding,
                old_rho_blinding,
                old_s_blinding,
                F0::rand(rng),
            ],
        );

        // Schnorr commitment for proving correctness of new account state which will become new leaf
        let t_acc_new = SchnorrCommitment::new(
            &Self::acc_new_gens(account_comm_key),
            vec![new_balance_blinding, new_rho_blinding, new_s_blinding],
        );

        // Schnorr commitment for proving correctness of nullifier
        let t_null = PokDiscreteLogProtocol::init(account.rho, old_rho_blinding, &nullifier_gen);

        // Schnorr commitment for knowledge of secret key in public key
        let t_pk = PokDiscreteLogProtocol::init(account.sk, F0::rand(rng), &pk_gen);

        t_r_leaf.challenge_contribution(&mut transcript)?;
        t_acc_new.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;
        t_pk.challenge_contribution(&pk_gen, &issuer_pk, &mut transcript)?;

        let prover_challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // TODO: Eliminate duplicate responses
        let resp_leaf = t_r_leaf.response(
            &[
                account.balance.into(),
                account.rho,
                account.randomness,
                rerandomization,
            ],
            &prover_challenge,
        )?;
        let resp_acc_new = t_acc_new.response(
            &[
                updated_account.balance.into(),
                updated_account.rho,
                updated_account.randomness,
            ],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_pk = t_pk.gen_proof(&prover_challenge);

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
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        issuer_pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
    ) -> Result<()> {
        if self.resp_leaf.len() != 4 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                4,
                self.resp_leaf.len(),
            ));
        }
        if self.resp_acc_new.len() != 3 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                3,
                self.resp_acc_new.len(),
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

        let nullifier_gen = account_comm_key.rho_gen();
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

        // Balance in leaf is less than the one in the new account commitment by `increase_bal_by`
        if self.resp_leaf.0[0] + (verifier_challenge * F0::from(increase_bal_by))
            != self.resp_acc_new.0[0]
        {
            return Err(Error::ProofVerificationError(
                "Balance increase verification failed".to_string(),
            ));
        }

        // rho matches the one in nullifier
        if self.resp_leaf.0[1] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho mismatch between leaf and nullifier".to_string(),
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
    ) -> [Affine<G0>; 4] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.randomness_gen(),
            account_tree_params.even_parameters.pc_gens.B_blinding,
        ]
    }

    fn acc_new_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> [Affine<G0>; 3] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.randomness_gen(),
        ]
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeePaymentProof<
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

    pub comm_new_bal: Affine<G0>,
    pub resp_bp: PokPedersenCommitment<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeePaymentProof<L, F0, F1, G0, G1>
{
    /// `nonce` is used to tie this fee payment proof to the corresponding txn and the eventual payee (relayer, etc) identity, eg. it can
    /// be constructed as b"<txn id>||<payee id>" and the verifier can ensure that the appropriate `nonce` is used
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        fee_amount: Balance,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        // Ensure accounts are consistent (same sk, asset_id)
        if account.sk != updated_account.sk {
            return Err(Error::ProofGenerationError(
                "Secret key mismatch between old and new account states".to_string(),
            ));
        }
        if account.asset_id != updated_account.asset_id {
            return Err(Error::ProofGenerationError(
                "Asset ID mismatch between old and new account states".to_string(),
            ));
        }
        if updated_account.balance != account.balance - fee_amount {
            return Err(Error::ProofGenerationError(
                "Balance decrease incorrect".to_string(),
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
        fee_amount.serialize_compressed(&mut extra_instance)?;
        updated_account_commitment.serialize_compressed(&mut extra_instance)?;
        account_tree_params.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // Need to prove that:
        // 1. nullifier is correctly formed
        // 2. sk is same in both old and new account commitment
        // 3. Old balance = new balance + fee_amount
        // 4. Range proof on new balance

        let sk_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let new_balance_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let new_rho_blinding = F0::rand(rng);
        let old_s_blinding = F0::rand(rng);
        let new_s_blinding = F0::rand(rng);
        let comm_bp_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.rho_gen();
        let nullifier = account.nullifier(&account_comm_key);

        let new_balance = F0::from(updated_account.balance);
        let asset_id = F0::from(account.asset_id);

        // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
        let t_r_leaf = SchnorrCommitment::new(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            vec![
                sk_blinding,
                asset_id_blinding,
                new_balance_blinding,
                old_rho_blinding,
                old_s_blinding,
                F0::rand(rng),
            ],
        );

        // Schnorr commitment for proving correctness of new account state which will become new leaf
        let t_acc_new = SchnorrCommitment::new(
            &Self::acc_new_gens(account_comm_key),
            vec![
                sk_blinding,
                asset_id_blinding,
                new_balance_blinding,
                new_rho_blinding,
                new_s_blinding,
            ],
        );

        // Schnorr commitment for proving correctness of nullifier
        let t_null = PokDiscreteLogProtocol::init(account.rho, old_rho_blinding, &nullifier_gen);

        t_r_leaf.challenge_contribution(&mut transcript)?;
        t_acc_new.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_prover below
        let _ = transcript;

        // Range proof on new balance to ensure it's non-negative. We need the range proof even when the fee_amount is public
        // since the balance has be in a given range.
        let (comm_new_bal, new_bal_var) = even_prover.commit(new_balance, comm_bp_blinding);
        range_proof(
            &mut even_prover,
            new_bal_var.into(),
            Some(updated_account.balance),
            FEE_AMOUNT_BITS.into(),
        )?;

        let t_bp = PokPedersenCommitmentProtocol::init(
            new_balance,
            new_balance_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            comm_bp_blinding,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );

        let mut transcript = even_prover.transcript();

        t_bp.challenge_contribution(
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &comm_new_bal,
            &mut transcript,
        )?;

        let prover_challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let resp_leaf = t_r_leaf.response(
            &[
                account.sk,
                asset_id,
                account.balance.into(),
                account.rho,
                account.randomness,
                rerandomization,
            ],
            &prover_challenge,
        )?;
        let resp_acc_new = t_acc_new.response(
            &[
                updated_account.sk,
                asset_id,
                new_balance,
                updated_account.rho,
                updated_account.randomness,
            ],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_proof(&prover_challenge);

        let resp_bp = t_bp.gen_proof(&prover_challenge);

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
                comm_new_bal,
                resp_bp,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
    ) -> Result<()> {
        if self.resp_leaf.len() != 6 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                6,
                self.resp_leaf.len(),
            ));
        }
        if self.resp_acc_new.len() != 5 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                5,
                self.resp_acc_new.len(),
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
        fee_amount.serialize_compressed(&mut extra_instance)?;
        updated_account_commitment.serialize_compressed(&mut extra_instance)?;
        account_tree_params.serialize_compressed(&mut extra_instance)?;
        account_comm_key.serialize_compressed(&mut extra_instance)?;

        verifier_transcript
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier_gen = account_comm_key.rho_gen();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)?;
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)?;
        self.resp_null.challenge_contribution(
            &nullifier_gen,
            &nullifier,
            &mut verifier_transcript,
        )?;

        // Drop reference to borrow even_verifier below
        let _ = verifier_transcript;

        let new_bal_var = even_verifier.commit(self.comm_new_bal);

        range_proof(
            &mut even_verifier,
            new_bal_var.into(),
            None,
            FEE_AMOUNT_BITS.into(),
        )?;

        let mut verifier_transcript = even_verifier.transcript();

        self.resp_bp.challenge_contribution(
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &self.comm_new_bal,
            &mut verifier_transcript,
        )?;

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        self.resp_leaf.is_valid(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            &self.re_randomized_path.get_rerandomized_leaf(),
            &self.t_r_leaf,
            &verifier_challenge,
        )?;

        self.resp_acc_new.is_valid(
            &Self::acc_new_gens(account_comm_key),
            &updated_account_commitment.0,
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

        // Sk and asset id in leaf match the ones in updated account commitment
        if self.resp_leaf.0[0] != self.resp_acc_new.0[0] {
            return Err(Error::ProofVerificationError(
                "Secret key in leaf does not match the one in updated account commitment"
                    .to_string(),
            ));
        }
        if self.resp_leaf.0[1] != self.resp_acc_new.0[1] {
            return Err(Error::ProofVerificationError(
                "Asset ID in leaf does not match the one in updated account commitment".to_string(),
            ));
        }

        // rho matches the one in nullifier
        if self.resp_leaf.0[3] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho mismatch between leaf and nullifier".to_string(),
            ));
        }

        // Balance in leaf is greater than the one in the new account commitment by `fee_amount`
        if self.resp_leaf.0[2]
            != self.resp_acc_new.0[2] + (verifier_challenge * F0::from(fee_amount))
        {
            return Err(Error::ProofVerificationError(
                "Balance decrease verification failed".to_string(),
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
    ) -> [Affine<G0>; 6] {
        [
            account_comm_key.sk_gen(),
            account_comm_key.asset_id_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.randomness_gen(),
            account_tree_params.even_parameters.pc_gens.B_blinding,
        ]
    }

    fn acc_new_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> [Affine<G0>; 5] {
        [
            account_comm_key.sk_gen(),
            account_comm_key.asset_id_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.randomness_gen(),
        ]
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account::tests::setup_gens;
    use crate::account_registration::tests::setup_comm_key;
    use crate::keys::{SigKey, keygen_sig};
    use curve_tree_relations::curve_tree::CurveTree;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;

    pub fn new_fee_account<R: CryptoRngCore, G: AffineRepr>(
        rng: &mut R,
        asset_id: AssetId,
        sk: SigKey<G>,
        balance: Balance,
    ) -> FeeAccountState<G> {
        FeeAccountState::new(rng, sk.0, balance, asset_id).unwrap()
    }

    #[test]
    fn fee_account_init() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

        let asset_id = 1;
        let balance = 1000;

        let (sk_i, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let fee_account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk_i.clone(), balance);
        assert_eq!(fee_account.asset_id, asset_id);
        assert_eq!(fee_account.balance, balance);
        assert_eq!(fee_account.sk, sk_i.0);

        fee_account.commit(account_comm_key).unwrap();
    }

    #[test]
    fn fee_account_registration() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key::<_, PallasA>(&mut rng);

        let asset_id = 1;
        let balance = 1000;

        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let fee_account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk_i, balance);
        let fee_account_comm = fee_account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce";

        let reg_proof = RegTxnProof::new(
            &mut rng,
            pk_i.0,
            &fee_account,
            fee_account_comm.clone(),
            nonce,
            account_comm_key.clone(),
        )
        .unwrap();

        reg_proof
            .verify(
                &mut rng,
                &pk_i.0,
                balance,
                asset_id,
                &fee_account_comm,
                nonce,
                account_comm_key,
            )
            .unwrap();
    }

    #[test]
    fn fee_account_topup_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 2000;
        let (account_tree_params, account_comm_key, _, _) = setup_gens::<_, NUM_GENS, L>(&mut rng);

        let asset_id = 1;

        // Issuer creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk_i, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // Add fee account commitment in curve tree
        // This tree size can be chosen independently of the one used for regular accounts and will likely be bigger
        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(3),
        );

        let increase_bal_by = 10;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account
            .get_state_for_topup(&mut rng, increase_bal_by)
            .unwrap();
        assert_eq!(updated_account.balance, account.balance + increase_bal_by);
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = FeeAccountTopupTxnProof::new(
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

        log::info!("For topup txn");
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
                    increase_bal_by + 10,
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
                    PallasA::rand(&mut rng),
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
    fn fee_payment_proof() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 2000;
        let (account_tree_params, account_comm_key, _, _) = setup_gens::<_, NUM_GENS, L>(&mut rng);

        let asset_id = 1;

        // Investor has fee payment account with some balance
        let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // This tree size can be chosen independently of the one used for regular accounts and will likely be bigger
        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(3),
        );

        let fee_amount = 10;

        // Or could be hash(a_txn_id, a_payee_id)
        let nonce = b"a_txn_id,a_payee_id";

        let clock = Instant::now();

        let updated_account = account.get_state_for_payment(&mut rng, fee_amount).unwrap();
        assert_eq!(updated_account.balance, account.balance - fee_amount);
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = FeePaymentProof::new(
            &mut rng,
            fee_amount,
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
                fee_amount,
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

        println!("For fee payment txn");
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );

        assert!(
            proof
                .verify(
                    fee_amount + 10,
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
    }
}
