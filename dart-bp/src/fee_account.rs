use crate::account::AccountCommitmentKeyTrait;
use crate::error::*;
use crate::util::{
    get_verification_tuples_with_rng, initialize_curve_tree_prover,
    initialize_curve_tree_prover_with_given_transcripts, initialize_curve_tree_verifier,
    initialize_curve_tree_verifier_with_given_transcripts, prove_with_rng,
    verify_given_verification_tuples,
};
use crate::{
    ACCOUNT_COMMITMENT_LABEL, ASSET_ID_LABEL, INCREASE_BAL_BY_LABEL, NONCE_LABEL, PK_LABEL,
    RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL,
    UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript,
};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::string::ToString;
use ark_std::{UniformRand, vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, R1CSProof, VerificationTuple};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance, FEE_BALANCE_BITS, MAX_FEE_BALANCE};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};

pub const FEE_AMOUNT_LABEL: &'static [u8; 10] = b"fee_amount";

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
        if amount + self.balance > MAX_FEE_BALANCE {
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
        let transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
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
        pk: G,
        account: &FeeAccountState<G>,
        account_commitment: FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: MerlinTranscript,
    ) -> Result<Self> {
        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            account.asset_id,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk
        );

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

    pub fn verify(
        &self,
        pk: &G,
        balance: Balance,
        asset_id: AssetId,
        account_commitment: &FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<()> {
        let transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        self.verify_with_given_transcript(
            pk,
            balance,
            asset_id,
            account_commitment,
            nonce,
            account_comm_key,
            transcript,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        pk: &G,
        balance: Balance,
        asset_id: AssetId,
        account_commitment: &FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: MerlinTranscript,
    ) -> Result<()> {
        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            asset_id,
            ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk
        );

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
    pub resp_acc_new: PartialSchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of issuer secret key using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_pk: PokDiscreteLog<Affine<G0>>,
    /// Commitment to the balance in new account commitment (which becomes new leaf) used with Bulletproof
    pub comm_new_bal: Affine<G0>,
    /// Response for Sigma protocol for proving knowledge of balance in `comm_new_bal`
    pub resp_bp: Partial2PokPedersenCommitment<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeeAccountTopupTxnProof<L, F0, F1, G0, G1>
{
    /// `pk` is the public key of the investor who is topping up his fee account
    /// and has the same secret key as the one in `account`
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &Affine<G0>,
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
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        Self::new_with_given_transcript(
            rng,
            pk,
            increase_bal_by,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            even_transcript,
            odd_transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        pk: &Affine<G0>,
        increase_bal_by: Balance,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_transcript: MerlinTranscript,
        odd_transcript: MerlinTranscript,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_correct_account_state(account, updated_account, increase_bal_by, false)?;

        let (mut even_prover, odd_prover, re_randomized_path, rerandomization) =
            initialize_curve_tree_prover_with_given_transcripts(
                rng,
                leaf_path,
                account_tree_params,
                even_transcript,
                odd_transcript,
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
            PK_LABEL,
            pk,
            ASSET_ID_LABEL,
            account.asset_id,
            INCREASE_BAL_BY_LABEL,
            increase_bal_by,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        // Need to prove that:
        // 1. nullifier is correctly formed
        // 2. sk in account commitment is the same as in the issuer's public key
        // 3. New balance = old balance + increase_bal_by
        // 4. Range proof on new balance

        let new_balance_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let new_rho_blinding = F0::rand(rng);
        let old_s_blinding = F0::rand(rng);
        let new_s_blinding = F0::rand(rng);
        let comm_bp_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.rho_gen();
        let pk_gen = account_comm_key.sk_gen();
        let nullifier = account.nullifier(&account_comm_key);

        let new_balance = F0::from(updated_account.balance);

        // Old account commitment = C = G0 * sk + G1 * old_bal + ...
        // New account commitment = C' = G0 * sk + G1 * new_bal + ...
        // And old_bal + increase_bal_by = new_bal where increase_bal_by is public
        // So the balance committed in C + G1 * increase_bal_by is the same as the balance committed in C'
        // and thus we prove that balance in C + G1 * increase_bal_by and C' are same

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
        t_pk.challenge_contribution(&pk_gen, &pk, &mut transcript)?;

        // Drop reference to borrow even_prover below
        let _ = transcript;

        // Range proof on new balance to ensure it's non-negative.
        let (comm_new_bal, new_bal_var) = even_prover.commit(new_balance, comm_bp_blinding);
        range_proof(
            &mut even_prover,
            new_bal_var.into(),
            Some(updated_account.balance),
            FEE_BALANCE_BITS.into(),
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

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let resp_leaf = t_r_leaf.response(
            &[
                new_balance,
                account.rho,
                account.randomness,
                rerandomization,
            ],
            &challenge,
        )?;

        // Response for other witnesses will already be generated in sigma protocol for the leaf
        let mut wits = BTreeMap::new();
        wits.insert(1, updated_account.rho);
        wits.insert(2, updated_account.randomness);
        let resp_acc_new = t_acc_new.partial_response(wits, &challenge)?;

        // Response for witness will already be generated in sigma protocol for the leaf
        let resp_null = t_null.gen_partial_proof();
        let resp_pk = t_pk.gen_proof(&challenge);

        // Response for witness will already be generated in sigma protocol for the new account commitment
        let resp_bp = t_bp.gen_partial2_proof(&challenge);

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
                comm_new_bal,
                resp_bp,
            },
            nullifier,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        pk: Affine<G0>,
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
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        self.verify_with_given_transcript(
            pk,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            rng,
            even_transcript,
            odd_transcript,
        )
    }

    pub fn verify_with_given_transcript<R: CryptoRngCore>(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        even_transcript: MerlinTranscript,
        odd_transcript: MerlinTranscript,
    ) -> Result<()> {
        let (even_tuple, odd_tuple) = self.verify_except_bp_with_given_transcript(
            pk,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            rng,
            even_transcript,
            odd_transcript,
        )?;

        verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params)
    }

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_except_bp<R: CryptoRngCore>(
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
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        self.verify_except_bp_with_given_transcript(
            issuer_pk,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            rng,
            even_transcript,
            odd_transcript,
        )
    }

    /// Verifies the proof except for final Bulletproof verification with given transcripts
    pub fn verify_except_bp_with_given_transcript<R: CryptoRngCore>(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        even_transcript: MerlinTranscript,
        odd_transcript: MerlinTranscript,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        if self.resp_leaf.len() != 4 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                4,
                self.resp_leaf.len(),
            ));
        }
        if self.resp_acc_new.responses.len() != 2 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                2,
                self.resp_acc_new.responses.len(),
            ));
        }

        let (mut even_verifier, odd_verifier) =
            initialize_curve_tree_verifier_with_given_transcripts(
                &self.re_randomized_path,
                root,
                account_tree_params,
                even_transcript,
                odd_transcript,
            );

        let mut transcript = even_verifier.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            self.re_randomized_path,
            NONCE_LABEL,
            nonce,
            PK_LABEL,
            pk,
            ASSET_ID_LABEL,
            asset_id,
            INCREASE_BAL_BY_LABEL,
            increase_bal_by,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.t_r_leaf.serialize_compressed(&mut transcript)?;
        self.t_acc_new.serialize_compressed(&mut transcript)?;
        self.resp_null
            .challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;
        self.resp_pk
            .challenge_contribution(&pk_gen, &pk, &mut transcript)?;

        // Drop reference to borrow even_verifier below
        let _ = transcript;

        let new_bal_var = even_verifier.commit(self.comm_new_bal);

        range_proof(
            &mut even_verifier,
            new_bal_var.into(),
            None,
            FEE_BALANCE_BITS.into(),
        )?;

        let mut transcript = even_verifier.transcript();

        self.resp_bp.challenge_contribution(
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &self.comm_new_bal,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let increase_bal_by = F0::from(increase_bal_by);

        let issuer_pk_proj = pk.into_group();
        let reduce = asset_id_comm + issuer_pk_proj;
        let y = self.re_randomized_path.get_rerandomized_leaf().into_group() - reduce
            + (account_comm_key.balance_gen() * increase_bal_by);
        self.resp_leaf.is_valid(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            &y.into_affine(),
            &self.t_r_leaf,
            &challenge,
        )?;

        let y = updated_account_commitment.0.into_group() - reduce;
        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(0, self.resp_leaf.0[0]);
        self.resp_acc_new.is_valid(
            &Self::acc_new_gens(account_comm_key),
            &y.into_affine(),
            &self.t_acc_new,
            &challenge,
            missing_resps,
        )?;

        // rho matches the one in nullifier
        if !self
            .resp_null
            .verify(&nullifier, &nullifier_gen, &challenge, &self.resp_leaf.0[1])
        {
            return Err(Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ));
        }
        if !self.resp_pk.verify(&pk, &pk_gen, &challenge) {
            return Err(Error::ProofVerificationError(
                "Issuer public key verification failed".to_string(),
            ));
        }

        if !self.resp_bp.verify(
            &self.comm_new_bal,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &challenge,
            &self.resp_leaf.0[0],
        ) {
            return Err(Error::ProofVerificationError(
                "Sigma protocol for Bulletproof commitment failed".to_string(),
            ));
        }

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &self.even_proof,
            &self.odd_proof,
            rng,
        )
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
    pub resp_acc_new: PartialSchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,

    pub comm_new_bal: Affine<G0>,
    pub resp_bp: Partial2PokPedersenCommitment<Affine<G0>>,
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
        ensure_correct_account_state(account, updated_account, fee_amount, true)?;

        let (mut even_prover, odd_prover, re_randomized_path, rerandomization) =
            initialize_curve_tree_prover(
                rng,
                TXN_EVEN_LABEL,
                TXN_ODD_LABEL,
                leaf_path,
                account_tree_params,
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
            ASSET_ID_LABEL,
            account.asset_id,
            FEE_AMOUNT_LABEL,
            fee_amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        // Need to prove that:
        // 1. nullifier is correctly formed
        // 2. sk is same in both old and new account commitment
        // 3. Old balance = new balance + fee_amount
        // 4. Range proof on new balance

        let sk_blinding = F0::rand(rng);
        let new_balance_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let new_rho_blinding = F0::rand(rng);
        let old_s_blinding = F0::rand(rng);
        let new_s_blinding = F0::rand(rng);
        let comm_bp_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.rho_gen();
        let nullifier = account.nullifier(&account_comm_key);

        let new_balance = F0::from(updated_account.balance);

        // Old account commitment = C = G0 * sk + G1 * old_bal + ...
        // New account commitment = C' = G0 * sk + G1 * new_bal + ...
        // And old_bal - fee_amount = new_bal where fee_amount is public
        // So the balance committed in C - G1 * fee_amount is the same as the balance committed in C'
        // and thus we prove that balance in C - G1 * fee_amount and C' are same

        // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
        let t_r_leaf = SchnorrCommitment::new(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            vec![
                sk_blinding,
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
            FEE_BALANCE_BITS.into(),
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

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let resp_leaf = t_r_leaf.response(
            &[
                account.sk,
                new_balance,
                account.rho,
                account.randomness,
                rerandomization,
            ],
            &challenge,
        )?;
        let mut wits = BTreeMap::new();
        wits.insert(2, updated_account.rho);
        wits.insert(3, updated_account.randomness);
        // Response for witnesses will already be generated in sigma protocol for the leaf
        let resp_acc_new = t_acc_new.partial_response(wits, &challenge)?;
        let resp_null = t_null.gen_partial_proof();

        // Response for witness will already be generated in sigma protocol for the new account commitment
        let resp_bp = t_bp.gen_partial2_proof(&challenge);

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
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
    ) -> Result<()> {
        let (even_tuple, odd_tuple) = self.verify_except_bp(
            asset_id,
            fee_amount,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            rng,
        )?;

        verify_given_verification_tuples(even_tuple, odd_tuple, account_tree_params)
    }

    /// Verifies the proof except for Bulletproof final verification
    pub fn verify_except_bp<R: CryptoRngCore>(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        if self.resp_leaf.len() != 5 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                5,
                self.resp_leaf.len(),
            ));
        }
        if self.resp_acc_new.responses.len() != 2 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                2,
                self.resp_acc_new.responses.len(),
            ));
        }

        let (mut even_verifier, odd_verifier) = initialize_curve_tree_verifier(
            TXN_EVEN_LABEL,
            TXN_ODD_LABEL,
            &self.re_randomized_path,
            root,
            account_tree_params,
        );

        let mut transcript = even_verifier.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            self.re_randomized_path,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            asset_id,
            FEE_AMOUNT_LABEL,
            fee_amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.rho_gen();

        self.t_r_leaf.serialize_compressed(&mut transcript)?;
        self.t_acc_new.serialize_compressed(&mut transcript)?;
        self.resp_null
            .challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_verifier below
        let _ = transcript;

        let new_bal_var = even_verifier.commit(self.comm_new_bal);

        range_proof(
            &mut even_verifier,
            new_bal_var.into(),
            None,
            FEE_BALANCE_BITS.into(),
        )?;

        let mut transcript = even_verifier.transcript();

        self.resp_bp.challenge_contribution(
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &self.comm_new_bal,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let fee_amount = F0::from(fee_amount);

        let y = self.re_randomized_path.get_rerandomized_leaf()
            - asset_id_comm
            - (account_comm_key.balance_gen() * fee_amount);
        self.resp_leaf.is_valid(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            &y.into_affine(),
            &self.t_r_leaf,
            &challenge,
        )?;

        let y = updated_account_commitment.0 - asset_id_comm;
        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(0, self.resp_leaf.0[0]);
        missing_resps.insert(1, self.resp_leaf.0[1]);
        self.resp_acc_new.is_valid(
            &Self::acc_new_gens(account_comm_key),
            &y.into_affine(),
            &self.t_acc_new,
            &challenge,
            missing_resps,
        )?;

        // rho matches the one in nullifier
        if !self
            .resp_null
            .verify(&nullifier, &nullifier_gen, &challenge, &self.resp_leaf.0[2])
        {
            return Err(Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ));
        }

        if !self.resp_bp.verify(
            &self.comm_new_bal,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &challenge,
            &self.resp_leaf.0[1],
        ) {
            return Err(Error::ProofVerificationError(
                "Sigma protocol for Bulletproof commitment failed".to_string(),
            ));
        }

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &self.even_proof,
            &self.odd_proof,
            rng,
        )
    }

    fn leaf_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        account_tree_params: &SelRerandParameters<G0, G1>,
    ) -> [Affine<G0>; 5] {
        [
            account_comm_key.sk_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.randomness_gen(),
            account_tree_params.even_parameters.pc_gens.B_blinding,
        ]
    }

    fn acc_new_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> [Affine<G0>; 4] {
        [
            account_comm_key.sk_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.randomness_gen(),
        ]
    }
}

fn ensure_correct_account_state<G: AffineRepr>(
    old_state: &FeeAccountState<G>,
    new_state: &FeeAccountState<G>,
    amount: Balance,
    has_balance_decreased: bool,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        // Ensure accounts are consistent (same sk, asset_id)
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
    use crate::account::tests::setup_gens;
    use crate::account_registration::tests::setup_comm_key;
    use crate::keys::{SigKey, keygen_sig};
    use crate::util::batch_verify_bp;
    use ark_std::cfg_into_iter;
    use curve_tree_relations::curve_tree::CurveTree;
    use std::time::Instant;

    #[cfg(feature = "parallel")]
    use rayon::prelude::*;

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
            &pk_i.0,
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
                asset_id,
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
                    asset_id,
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

        assert!(
            proof
                .verify(
                    asset_id,
                    fee_amount,
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

        assert!(
            proof
                .verify(
                    asset_id + 1,
                    fee_amount,
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

    #[test]
    fn batch_fee_payment_proofs() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 512;
        let (account_tree_params, account_comm_key, _, _) = setup_gens::<_, NUM_GENS, L>(&mut rng);

        let asset_id = 1;

        let batch_size = 5;

        let mut accounts = Vec::with_capacity(batch_size);
        let mut account_comms = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let balance = 1000;
            let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk, balance);
            let account_comm = account.commit(account_comm_key.clone()).unwrap();
            accounts.push(account);
            account_comms.push(account_comm);
        }

        let fee_amount = 10;

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(4),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i]
                .get_state_for_payment(&mut rng, fee_amount)
                .unwrap();
            assert_eq!(updated_account.balance, accounts[i].balance - fee_amount);
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0);
            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        // Create unique nonces for each proof
        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("test_nonce_{}", i).into_bytes())
            .collect();

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (proof, nullifier) = FeePaymentProof::new(
                &mut rng,
                fee_amount,
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();
            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        // NOTE: Rather than creating fresh thread rngs, use seeded ChaCha rngs from the original rng

        let clock = Instant::now();

        let res = cfg_into_iter!(0..batch_size)
            .map(|i| {
                let mut rng_ = rand::thread_rng();
                proofs[i].verify(
                    asset_id,
                    fee_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng_,
                )
            })
            .map(|r| r)
            .collect::<Vec<_>>();

        for r in res {
            r.unwrap();
        }
        // for i in 0..batch_size {
        //     proofs[i]
        //         .verify(
        //             asset_id,
        //             fee_amount,
        //             updated_account_comms[i],
        //             nullifiers[i],
        //             &root,
        //             &nonces[i],
        //             &account_tree_params,
        //             account_comm_key.clone(),
        //             &mut rng,
        //         )
        //         .unwrap();
        // }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let res = cfg_into_iter!(0..batch_size)
            .map(|i| {
                let mut rng_ = rand::thread_rng();
                proofs[i].verify_except_bp(
                    asset_id,
                    fee_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng_,
                )
            })
            .collect::<Vec<_>>();
        for res in res {
            let (even, odd) = res.unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        // These can also be done in parallel
        // for i in 0..batch_size {
        //     let (even, odd) = proofs[i]
        //         .verify_except_bp(
        //             asset_id,
        //             fee_amount,
        //             updated_account_comms[i],
        //             nullifiers[i],
        //             &root,
        //             &nonces[i],
        //             &account_tree_params,
        //             account_comm_key.clone(),
        //             &mut rng,
        //         )
        //         .unwrap();
        //     even_tuples.push(even);
        //     odd_tuples.push(odd);
        // }

        let pre_msm_check = clock.elapsed();

        let clock = Instant::now();
        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

        let batch_verifier_time = pre_msm_check + clock.elapsed();

        println!(
            "For {batch_size} fee payment proofs, verifier time = {:?}, pre_msm_check time {:?}, total batch verifier time {:?}",
            verifier_time, pre_msm_check, batch_verifier_time
        );
    }

    // Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled

    #[cfg(feature = "ignore_prover_input_sanitation")]
    mod input_sanitation_disabled {
        use super::*;

        #[test]
        fn increase_balance_more_than_expected_in_topup_txn() {
            // A fee account sends FeeAccountTopupTxnProof but increases the balance more than the expected increase_bal_by amount. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 2000;
            let (account_tree_params, account_comm_key, _, _) =
                setup_gens::<_, NUM_GENS, L>(&mut rng);

            let asset_id = 1;

            // Issuer creates keys
            let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

            let balance = 1000;
            let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk_i, balance);
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            // Add fee account commitment in curve tree
            let set = vec![account_comm.0];
            let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
                &set,
                &account_tree_params,
                Some(3),
            );

            let increase_bal_by = 10;

            let nonce = b"test-nonce";

            // Create updated account but increase balance more than expected
            let mut updated_account = account
                .get_state_for_topup(&mut rng, increase_bal_by)
                .unwrap();
            updated_account.balance = account.balance + 50; // Add extra on top of the actual increase amount

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0);
            let root = account_tree.root_node();

            let (proof, nullifier) = FeeAccountTopupTxnProof::new(
                &mut rng,
                &pk_i.0,
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

            assert!(
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
                    .is_err()
            );
        }

        #[test]
        fn decrease_balance_less_than_expected_in_payment_txn() {
            // A fee account sends FeePaymentProof but decreases the balance less than the expected fee_amount. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 2000;
            let (account_tree_params, account_comm_key, _, _) =
                setup_gens::<_, NUM_GENS, L>(&mut rng);

            let asset_id = 1;

            // Investor has fee payment account with some balance
            let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let balance = 1000;
            let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk, balance);
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            let set = vec![account_comm.0];
            let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
                &set,
                &account_tree_params,
                Some(3),
            );

            let fee_amount = 10;
            let nonce = b"a_txn_id,a_payee_id";

            // Create updated account but decrease balance less than expected
            let mut updated_account = account.get_state_for_payment(&mut rng, fee_amount).unwrap();
            updated_account.balance = account.balance + 5; // Decrease by 5 less than the actual fee amount

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

            assert!(
                proof
                    .verify(
                        asset_id,
                        fee_amount,
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
}
