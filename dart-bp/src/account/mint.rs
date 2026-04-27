use crate::AUTH_PROOF_LABEL;
use crate::account::common::balance::ensure_correct_balance_change;
use crate::account::common::ensure_same_accounts;
use crate::account::state::{CURRENT_RANDOMNESS_GEN_INDEX, CURRENT_RHO_GEN_INDEX, NUM_GENERATORS};
use crate::account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment};
use crate::auth_proofs::{AuthProofOnlySks, AuthProofOnlySksProtocol};
use crate::util::{
    BPProof, bp_gens_for_vec_commitment, enforce_constraints_for_randomness_relations,
    get_verification_tuples_with_rng, handle_verification_tuples, prove_with_rng, verify_with_rng,
};
use crate::{
    ASSET_ID_LABEL, Error, ID_LABEL, INCREASE_BAL_BY_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL,
    ROOT_LABEL, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL,
    UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript, error::Result,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier};
use bulletproofs::{BulletproofGens, PedersenGens};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::PokDiscreteLogProtocol;
use schnorr_pok::partial::{PartialPokDiscreteLog, PartialSchnorrResponse};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;

pub const ISSUER_PK_LABEL: &'static [u8; 9] = b"issuer_pk";
pub const ISSUER_PK_ENC_LABEL: &'static [u8; 9] = b"issuer_pk";

// Split proof follows similar approach as top up txn of fee but here there a are 2 public keys and not 1

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MintTxnProofPartial<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    const L: usize,
> {
    pub r1cs_proof: Option<BPProof<G0, G1>>,
    /// This contains the old account state, but re-randomized (as re-randomized leaf)
    pub re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    /// Commitment to randomness for proving knowledge of re-randomized old state commitment (leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_old: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized old state commitment (leaf) using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_old: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: PartialSchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,
    /// Commitment to the values committed in Bulletproofs
    pub comm_bp: Affine<G0>,
    /// Commitment to randomness for proving knowledge of values committed in Bulletproofs commitment (step 1 of Schnorr)
    pub t_bp: Affine<G0>,
    /// Response for proving knowledge of values committed in Bulletproofs (step 3 of Schnorr)
    pub resp_bp: PartialSchnorrResponse<Affine<G0>>,
}

pub struct MintTxnProofPartialProtocol<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    const L: usize,
> {
    t_acc_old: SchnorrCommitment<Affine<G0>>,
    t_acc_new: SchnorrCommitment<Affine<G0>>,
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_bp: SchnorrCommitment<Affine<G0>>,
    re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    comm_bp: Affine<G0>,
    // Witnesses needed for gen_proof
    balance: F0,
    counter: F0,
    rho: F0,
    current_rho: F0,
    randomness: F0,
    current_randomness: F0,
    rerandomization: F0,
    updated_current_rho: F0,
    updated_current_randomness: F0,
    comm_bp_blinding: F0,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MintTxnProofPartialProtocol<F0, F1, G0, G1, L>
{
    pub fn init_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (re_randomized_path, rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<_, Parameters0, Parameters1>(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
            )?;

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
            issuer_aff_pk,
            ISSUER_PK_ENC_LABEL,
            issuer_enc_pk,
            ID_LABEL,
            account.id,
            ASSET_ID_LABEL,
            account.asset_id,
            INCREASE_BAL_BY_LABEL,
            increase_bal_by,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let mut counter_blinding = F0::rand(rng);
        let mut new_balance_blinding = F0::rand(rng);
        let mut initial_rho_blinding = F0::rand(rng);
        let mut old_rho_blinding = F0::rand(rng);
        let mut new_rho_blinding = F0::rand(rng);
        let mut initial_s_blinding = F0::rand(rng);
        let mut old_s_blinding = F0::rand(rng);
        let mut new_s_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.current_rho_gen();
        let nullifier = (nullifier_gen * account.current_rho).into_affine();

        // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
        let t_acc_old = SchnorrCommitment::new(
            &MintTxnProof::<L, F0, F1, G0, G1>::leaf_gens(
                account_comm_key.clone(),
                account_tree_params
                    .even_parameters
                    .sl_params
                    .pc_gens()
                    .B_blinding,
            ),
            vec![
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                old_rho_blinding,
                initial_s_blinding,
                old_s_blinding,
                F0::rand(rng),
            ],
        );

        // Schnorr commitment for proving correctness of new account state which will become new leaf
        let t_acc_new = SchnorrCommitment::new(
            &MintTxnProof::<L, F0, F1, G0, G1>::acc_new_gens(&account_comm_key),
            vec![
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                new_rho_blinding,
                initial_s_blinding,
                new_s_blinding,
            ],
        );

        // Schnorr commitment for proving correctness of nullifier
        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, old_rho_blinding, &nullifier_gen);

        t_acc_old.challenge_contribution(&mut transcript)?;
        t_acc_new.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_prover below
        let _ = transcript;

        let comm_bp_blinding = F0::rand(rng);
        let (comm_bp, mut vars) = even_prover.commit_vec(
            &[
                account.rho,
                account.current_rho,
                updated_account.current_rho,
                account.randomness,
                account.current_randomness,
                updated_account.current_randomness,
            ],
            comm_bp_blinding,
            account_tree_params.even_parameters.bp_gens(),
        );
        enforce_constraints_for_randomness_relations(even_prover, &mut vars);

        let mut transcript = even_prover.transcript();

        let t_bp = SchnorrCommitment::new(
            &MintTxnProof::<L, F0, F1, G0, G1>::bp_gens_vec(
                account_tree_params.even_parameters.pc_gens(),
                account_tree_params.even_parameters.bp_gens(),
            ),
            vec![
                F0::rand(rng),
                initial_rho_blinding,
                old_rho_blinding,
                new_rho_blinding,
                initial_s_blinding,
                old_s_blinding,
                new_s_blinding,
            ],
        );

        t_bp.challenge_contribution(&mut transcript)?;

        counter_blinding.zeroize();
        new_balance_blinding.zeroize();
        initial_rho_blinding.zeroize();
        old_rho_blinding.zeroize();
        new_rho_blinding.zeroize();
        initial_s_blinding.zeroize();
        old_s_blinding.zeroize();
        new_s_blinding.zeroize();

        Ok((
            Self {
                t_acc_old,
                t_acc_new,
                t_null,
                t_bp,
                re_randomized_path,
                comm_bp,
                balance: account.balance.into(),
                counter: account.counter.into(),
                rho: account.rho,
                current_rho: account.current_rho,
                randomness: account.randomness,
                current_randomness: account.current_randomness,
                rerandomization,
                updated_current_rho: updated_account.current_rho,
                updated_current_randomness: updated_account.current_randomness,
                comm_bp_blinding,
            },
            nullifier,
        ))
    }

    pub fn gen_proof(mut self, challenge: &F0) -> Result<MintTxnProofPartial<F0, F1, G0, G1, L>> {
        let mut wits = [
            self.balance,
            self.counter,
            self.rho,
            self.current_rho,
            self.randomness,
            self.current_randomness,
            self.rerandomization,
        ];
        let resp_acc_old = self.t_acc_old.response(&wits, challenge)?;
        Zeroize::zeroize(&mut wits);

        // Response for other witnesses will already be generated in sigma protocol for leaf
        let mut wits = BTreeMap::new();
        // -2 since sk (proved in pk) and asset id knowledge is not being proven
        wits.insert(CURRENT_RHO_GEN_INDEX - 2, self.updated_current_rho);
        wits.insert(
            CURRENT_RANDOMNESS_GEN_INDEX - 2,
            self.updated_current_randomness,
        );
        let resp_acc_new = self.t_acc_new.partial_response(wits, challenge)?;

        // Response for witness will already be generated in sigma protocol for leaf
        let resp_null = self.t_null.gen_partial_proof();

        // Response for other witnesses will already be generated in sigma protocol for leaf, and new account commitment
        let mut w = BTreeMap::new();
        w.insert(0, self.comm_bp_blinding);
        let resp_bp = self.t_bp.partial_response(w, challenge)?;

        self.comm_bp_blinding.zeroize();
        self.rerandomization.zeroize();

        Ok(MintTxnProofPartial {
            r1cs_proof: None,
            re_randomized_path: self.re_randomized_path,
            t_acc_old: self.t_acc_old.t,
            t_acc_new: self.t_acc_new.t,
            resp_acc_old,
            resp_acc_new,
            resp_null,
            comm_bp: self.comm_bp,
            t_bp: self.t_bp.t,
            resp_bp,
        })
    }

    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(MintTxnProofPartial<F0, F1, G0, G1, L>, Affine<G0>)> {
        let (proto, mut even_prover, odd_prover, nullifier) =
            Self::init::<_, Parameters0, Parameters1>(
                rng,
                issuer_aff_pk,
                issuer_enc_pk,
                increase_bal_by,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;

        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        let mut partial = proto.gen_proof(&challenge_h)?;

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((partial, nullifier))
    }

    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Self,
        Prover<'a, MerlinTranscript, Affine<G0>>,
        Prover<'a, MerlinTranscript, Affine<G1>>,
        Affine<G0>,
    )> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            account_tree_params.even_parameters.pc_gens(),
            transcript_even,
        );
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover =
            Prover::new(account_tree_params.odd_parameters.pc_gens(), transcript_odd);

        let (proto, nullifier) = Self::init_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            issuer_aff_pk,
            issuer_enc_pk,
            increase_bal_by,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            &mut even_prover,
            &mut odd_prover,
        )?;

        Ok((proto, even_prover, odd_prover, nullifier))
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MintTxnProofPartial<F0, F1, G0, G1, L>
{
    pub fn challenge_contribution_with_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
    ) -> Result<()> {
        self.re_randomized_path
            .select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
                root,
                even_verifier,
                odd_verifier,
                account_tree_params,
            )?;

        let mut transcript = even_verifier.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            self.re_randomized_path,
            NONCE_LABEL,
            nonce,
            ISSUER_PK_LABEL,
            issuer_aff_pk,
            ISSUER_PK_ENC_LABEL,
            issuer_enc_pk,
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

        self.t_acc_old.serialize_compressed(&mut transcript)?;
        self.t_acc_new.serialize_compressed(&mut transcript)?;
        self.resp_null
            .challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_verifier below
        let _ = transcript;

        let mut vars = even_verifier.commit_vec(6, self.comm_bp);
        enforce_constraints_for_randomness_relations(even_verifier, &mut vars);

        let mut transcript = even_verifier.transcript();

        self.t_bp.serialize_compressed(&mut transcript)?;

        Ok(())
    }

    pub fn verify_with_challenge<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        challenge: &F0,
    ) -> Result<()> {
        if self.resp_acc_old.len() != NUM_GENERATORS - 3 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS - 3,
                self.resp_acc_old.len(),
            ));
        }
        if self.resp_acc_new.responses.len() != 2 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                2,
                self.resp_acc_new.responses.len(),
            ));
        }
        let resp_acc_new_3 = self
            .resp_acc_new
            .responses
            .get(&3)
            .copied()
            .ok_or_else(|| {
                Error::ProofVerificationError("resp_acc_new missing key 3".to_string())
            })?;
        let resp_acc_new_5 = self
            .resp_acc_new
            .responses
            .get(&5)
            .copied()
            .ok_or_else(|| {
                Error::ProofVerificationError("resp_acc_new missing key 5".to_string())
            })?;

        if self.resp_bp.responses.len() != 1 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                1,
                self.resp_bp.responses.len(),
            ));
        }
        if !self.resp_bp.responses.contains_key(&0) {
            return Err(Error::ProofVerificationError(
                "resp_bp missing key 0".to_string(),
            ));
        }

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let increase_bal_by = F0::from(increase_bal_by);

        let issuer_pk_proj = issuer_aff_pk.into_group();
        let issuer_pk_enc_proj = issuer_enc_pk.into_group();
        let y = self.re_randomized_path.path.get_rerandomized_leaf()
            - asset_id_comm
            - issuer_pk_proj
            - issuer_pk_enc_proj
            - (account_comm_key.id_gen() * id);
        self.resp_acc_old.is_valid(
            &MintTxnProof::<L, F0, F1, G0, G1>::leaf_gens(
                account_comm_key.clone(),
                account_tree_params
                    .even_parameters
                    .sl_params
                    .pc_gens()
                    .B_blinding,
            ),
            &y.into_affine(),
            &self.t_acc_old,
            challenge,
        )?;

        let y = updated_account_commitment.0
            - asset_id_comm
            - issuer_pk_proj
            - issuer_pk_enc_proj
            - (account_comm_key.id_gen() * id)
            - (account_comm_key.balance_gen() * increase_bal_by);
        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(0, self.resp_acc_old.0[0]);
        missing_resps.insert(1, self.resp_acc_old.0[1]);
        missing_resps.insert(2, self.resp_acc_old.0[2]);
        missing_resps.insert(4, self.resp_acc_old.0[4]);
        self.resp_acc_new.is_valid(
            &MintTxnProof::<L, F0, F1, G0, G1>::acc_new_gens(&account_comm_key),
            &y.into_affine(),
            &self.t_acc_new,
            challenge,
            missing_resps,
        )?;

        self.resp_null
            .verify(
                &nullifier,
                &account_comm_key.current_rho_gen(),
                challenge,
                &self.resp_acc_old.0[3],
            )
            .map_err(|_| {
                Error::ProofVerificationError("Nullifier verification failed".to_string())
            })?;

        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(1, self.resp_acc_old.0[2]);
        missing_resps.insert(2, self.resp_acc_old.0[3]);
        missing_resps.insert(3, resp_acc_new_3);
        missing_resps.insert(4, self.resp_acc_old.0[4]);
        missing_resps.insert(5, self.resp_acc_old.0[5]);
        missing_resps.insert(6, resp_acc_new_5);
        self.resp_bp.is_valid(
            &MintTxnProof::<L, F0, F1, G0, G1>::bp_gens_vec(
                account_tree_params.even_parameters.pc_gens(),
                account_tree_params.even_parameters.bp_gens(),
            ),
            &self.comm_bp,
            &self.t_bp,
            challenge,
            missing_resps,
        )?;

        Ok(())
    }

    pub fn verify<Parameters0: DiscreteLogParameters, Parameters1: DiscreteLogParameters>(
        &self,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
    )> {
        let (mut even_verifier, odd_verifier) = self
            .challenge_contribution::<Parameters0, Parameters1>(
                issuer_aff_pk,
                issuer_enc_pk,
                id,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
            )?;
        let challenge_h = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        self.verify_with_challenge::<Parameters0, Parameters1>(
            issuer_aff_pk,
            issuer_enc_pk,
            id,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            &challenge_h,
        )?;
        Ok((even_verifier, odd_verifier))
    }

    pub fn challenge_contribution<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
    )> {
        let mut even_verifier = Verifier::new(MerlinTranscript::new(TXN_EVEN_LABEL));
        let mut odd_verifier = Verifier::new(MerlinTranscript::new(TXN_ODD_LABEL));
        self.challenge_contribution_with_verifier::<Parameters0, Parameters1>(
            issuer_aff_pk,
            issuer_enc_pk,
            id,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            &mut even_verifier,
            &mut odd_verifier,
        )?;
        Ok((even_verifier, odd_verifier))
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MintTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub partial: MintTxnProofPartial<F0, F1, G0, G1, { L }>,
    /// Commitment to randomness and response for proving knowledge of issuer secret key using Schnorr protocol (step 1 and 3 of Schnorr)
    // pub resp_pk_aff: PokDiscreteLog<Affine<G0>>,
    pub auth_proof: AuthProofOnlySks<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MintTxnProof<L, F0, F1, G0, G1>
{
    /// `issuer_pk` has the same secret key as the one in `account`
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        issuer_aff_sk: G0::ScalarField,
        issuer_enc_sk: G0::ScalarField,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

        Self::new_with_given_transcript::<_, Parameters0, Parameters1>(
            rng,
            issuer_aff_sk,
            issuer_enc_sk,
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

    pub fn new_with_given_transcript<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        issuer_aff_sk: G0::ScalarField,
        issuer_enc_sk: G0::ScalarField,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        transcript_even: MerlinTranscript,
        transcript_odd: MerlinTranscript,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_same_accounts(account, updated_account, true)?;
        ensure_correct_balance_change(account, updated_account, increase_bal_by, false)?;

        let mut even_prover = Prover::new(
            account_tree_params.even_parameters.pc_gens(),
            transcript_even,
        );
        let mut odd_prover =
            Prover::new(account_tree_params.odd_parameters.pc_gens(), transcript_odd);

        let aff_key_gen = account_comm_key.sk_gen();
        let enc_key_gen = account_comm_key.sk_enc_gen();

        let issuer_aff_pk = account.pk_aff();
        let issuer_enc_pk = account.pk_enc();
        let (partial_proto, nullifier) =
            MintTxnProofPartialProtocol::init_with_given_prover::<_, Parameters0, Parameters1>(
                rng,
                issuer_aff_pk,
                issuer_enc_pk,
                increase_bal_by,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                &mut even_prover,
                &mut odd_prover,
            )?;

        let mut transcript = even_prover.transcript();
        let auth_protocol = AuthProofOnlySksProtocol::init(
            rng,
            issuer_aff_sk,
            issuer_enc_sk,
            &issuer_aff_pk,
            &issuer_enc_pk,
            &aff_key_gen,
            &enc_key_gen,
            &mut transcript,
        )?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let partial = partial_proto.gen_proof(&challenge)?;
        let auth_proof = auth_protocol.gen_proof(&challenge);

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;

        Ok((
            Self {
                auth_proof,
                partial: {
                    let mut p = partial;
                    p.r1cs_proof = Some(BPProof {
                        even_proof,
                        odd_proof,
                    });
                    p
                },
            },
            nullifier,
        ))
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
    ) -> Result<()> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);

        self.verify_with_given_transcript::<_, Parameters0, Parameters1>(
            issuer_aff_pk,
            issuer_enc_pk,
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

    pub fn verify_with_given_transcript<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        transcript_even: MerlinTranscript,
        transcript_odd: MerlinTranscript,
    ) -> Result<()> {
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        let sk_gen = account_comm_key.sk_gen();
        let enc_key_gen = account_comm_key.sk_enc_gen();

        // Partial challenge contribution: re-rand gadget, public inputs, partial T-values, BP
        self.partial
            .challenge_contribution_with_verifier::<Parameters0, Parameters1>(
                issuer_aff_pk,
                issuer_enc_pk,
                id,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                &mut even_verifier,
                &mut odd_verifier,
            )?;

        // Auth challenge contribution + challenge derivation
        let mut transcript = even_verifier.transcript();
        self.auth_proof.challenge_contribution(
            &issuer_aff_pk,
            &issuer_enc_pk,
            &sk_gen,
            &enc_key_gen,
            &mut transcript,
        )?;
        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Verify partial sigma protocols
        self.partial
            .verify_with_challenge::<Parameters0, Parameters1>(
                issuer_aff_pk,
                issuer_enc_pk,
                id,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                account_tree_params,
                account_comm_key,
                &challenge,
            )?;

        // Verify auth sigma protocol
        self.auth_proof.verify_given_challenge(
            &issuer_aff_pk,
            &issuer_enc_pk,
            &sk_gen,
            &enc_key_gen,
            &challenge,
            None,
        )?;

        let r1cs_proof =
            self.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        Ok(verify_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.odd_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?)
    }

    pub fn verify_split<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_aff_pk: Affine<G0>,
        issuer_enc_pk: Affine<G0>,
        id: G0::ScalarField,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let sk_gen = account_comm_key.sk_gen();
        let sk_enc_gen = account_comm_key.sk_enc_gen();

        let (mut even_verifier, odd_verifier) = self
            .partial
            .challenge_contribution::<Parameters0, Parameters1>(
                issuer_aff_pk,
                issuer_enc_pk,
                id,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                &root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
            )?;

        let challenge_h_v = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v.serialize_compressed(&mut challenge_h_v_bytes)?;
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        self.auth_proof.verify(
            issuer_aff_pk,
            issuer_enc_pk,
            &ledger_nonce_v,
            &sk_gen,
            &sk_enc_gen,
            None,
        )?;

        let mut auth_proof_bytes = Vec::new();
        self.auth_proof
            .serialize_compressed(&mut auth_proof_bytes)?;
        even_verifier
            .transcript()
            .append_message(AUTH_PROOF_LABEL, &auth_proof_bytes);
        let challenge_h_final_v = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        self.partial
            .verify_with_challenge::<Parameters0, Parameters1>(
                issuer_aff_pk,
                issuer_enc_pk,
                id,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                account_tree_params,
                account_comm_key,
                &challenge_h_final_v,
            )?;

        let r1cs =
            self.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        let (even_tuple, odd_tuple) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs.even_proof,
            &r1cs.odd_proof,
            rng,
        )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    fn leaf_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        B_blinding: Affine<G0>,
    ) -> [Affine<G0>; NUM_GENERATORS - 3] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_comm_key.current_randomness_gen(),
            B_blinding,
        ]
    }

    fn acc_new_gens(
        account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> [Affine<G0>; NUM_GENERATORS - 4] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_comm_key.current_randomness_gen(),
        ]
    }

    fn bp_gens_vec(
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
    ) -> [Affine<G0>; 7] {
        let mut gens = bp_gens_for_vec_commitment(6, bp_gens);
        [
            pc_gens.B_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account::common::ensure_same_accounts;
    use crate::account::tests::{
        get_tree_with_account_comm, get_tree_with_commitment, setup_gens_new,
    };
    use crate::account_registration::tests::new_account;
    use crate::keys::{keygen_enc, keygen_sig};
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use ark_pallas::Fr as PallasFr;
    use ark_std::UniformRand;
    use std::time::Instant;

    #[test]
    fn increase_supply_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;

        // Issuer creates keys
        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, account_comm_key.sk_enc_gen());

        let id = PallasFr::rand(&mut rng);
        let (account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id.clone());

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
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
        assert_eq!(updated_account.randomness, account.randomness);
        assert_eq!(
            updated_account.current_randomness,
            account.current_randomness * account.randomness
        );
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = MintTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
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
            .verify::<_, PallasParams, VestaParams>(
                pk_aff.0,
                pk_enc.0,
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

        println!("For mint txn");
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn increase_supply_txn_parallel() {
        // W2 (Parallel): Host creates partial mint proof, Ledger creates auth proof independently.
        // Both use their own transcripts; challenges are independent.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");
        let asset_id = 1;
        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, account_comm_key.sk_enc_gen());
        let id = PallasFr::rand(&mut rng);
        let (account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id.clone());

        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let account_tree =
            get_tree_with_commitment::<L, _>(account_comm.clone(), &account_tree_params, 6);

        let increase_bal_by = 10;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_mint(increase_bal_by).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        ensure_same_accounts(&account, &updated_account, true).unwrap();
        ensure_correct_balance_change(&account, &updated_account, increase_bal_by, false).unwrap();

        let sk_gen = account_comm_key.sk_gen();
        let sk_enc_gen = account_comm_key.sk_enc_gen();
        let (partial, nullifier) =
            MintTxnProofPartialProtocol::new::<_, PallasParams, VestaParams>(
                &mut rng,
                pk_aff.0,
                pk_enc.0,
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

        //  Ledger side: own AUTH_TXN_LABEL transcript, independently
        let auth_proof = AuthProofOnlySks::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            pk_aff.0,
            pk_enc.0,
            nonce,
            &sk_gen,
            &sk_enc_gen,
        )
        .unwrap();

        let proof = MintTxnProof {
            auth_proof,
            partial,
        };

        //  verify each side with its own independent challenge
        let (even_verifier, odd_verifier) = proof
            .partial
            .verify::<PallasParams, VestaParams>(
                pk_aff.0,
                pk_enc.0,
                id.clone(),
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        // Verify auth proof using its own AUTH_TXN_LABEL transcript
        proof
            .auth_proof
            .verify(pk_aff.0, pk_enc.0, nonce, &sk_gen, &sk_enc_gen, None)
            .unwrap();

        let r1cs_proof = proof.partial.r1cs_proof.as_ref().unwrap();
        verify_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.odd_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            &mut rng,
        )
        .unwrap();
    }

    #[test]
    fn increase_supply_txn_sequential() {
        // W3 (Sequential): Host derives partial challenge first, sends it to Ledger.
        // Ledger uses ledger_nonce = [challenge_h_bytes || original_nonce] for its own AUTH_TXN_LABEL transcript.
        // Verifier replicates: derive partial challenge, verify partial, recompute ledger nonce, verify auth.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");
        let asset_id = 1;
        let (sk_aff, pk_aff) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, account_comm_key.sk_enc_gen());
        let id = PallasFr::rand(&mut rng);
        let (account, _, _, _) = new_account(&mut rng, asset_id, pk_aff, pk_enc, id.clone());

        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let account_tree =
            get_tree_with_commitment::<L, _>(account_comm.clone(), &account_tree_params, 6);

        let increase_bal_by = 10;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_mint(increase_bal_by).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host pre-challenge phase
        ensure_same_accounts(&account, &updated_account, true).unwrap();
        ensure_correct_balance_change(&account, &updated_account, increase_bal_by, false).unwrap();

        let sk_gen = account_comm_key.sk_gen();
        let sk_enc_gen = account_comm_key.sk_enc_gen();
        let (protocol, mut even_prover, odd_prover, nullifier) =
            MintTxnProofPartialProtocol::init::<_, PallasParams, VestaParams>(
                &mut rng,
                pk_aff.0,
                pk_enc.0,
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

        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

        //  Host sends challenge_h bytes to Ledger
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        let auth_proof = AuthProofOnlySks::new(
            &mut rng,
            sk_aff.0,
            sk_enc.0,
            pk_aff.0,
            pk_enc.0,
            &ledger_nonce,
            &sk_gen,
            &sk_enc_gen,
        )
        .unwrap();

        //  Host hashes auth_proof into the transcript to derive an updated challenge
        let mut auth_proof_bytes = Vec::new();
        auth_proof
            .serialize_compressed(&mut auth_proof_bytes)
            .unwrap();
        even_prover
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes);
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

        //  Host post-challenge phase
        let mut partial = protocol.gen_proof(&challenge_h_final).unwrap();
        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rng,
        )
        .unwrap();
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        let proof = MintTxnProof {
            auth_proof,
            partial,
        };

        //  derive partial challenge, verify partial, recompute ledger nonce, verify auth
        let (mut even_verifier, odd_verifier) = proof
            .partial
            .challenge_contribution::<PallasParams, VestaParams>(
                pk_aff.0,
                pk_enc.0,
                id.clone(),
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        let challenge_h_v = even_verifier
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

        // Verifier recomputes ledger nonce from the partial challenge
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        proof
            .auth_proof
            .verify(
                pk_aff.0,
                pk_enc.0,
                &ledger_nonce_v,
                &sk_gen,
                &sk_enc_gen,
                None,
            )
            .unwrap();

        // Verifier hashes auth_proof into the transcript to derive the updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        proof
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        even_verifier
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = even_verifier
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

        proof
            .partial
            .verify_with_challenge::<PallasParams, VestaParams>(
                pk_aff.0,
                pk_enc.0,
                id.clone(),
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &account_tree_params,
                account_comm_key.clone(),
                &challenge_h_final_v,
            )
            .unwrap();

        let r1cs_proof = proof.partial.r1cs_proof.as_ref().unwrap();
        verify_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.odd_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            &mut rng,
        )
        .unwrap();
    }
}
