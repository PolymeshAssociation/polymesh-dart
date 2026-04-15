use crate::account::common::balance::ensure_correct_balance_change;
use crate::account::common::{ensure_same_accounts, ensure_same_accounts_without_sk};
use crate::account::state::{CURRENT_RANDOMNESS_GEN_INDEX, CURRENT_RHO_GEN_INDEX, NUM_GENERATORS};
use crate::account::{
    AccountCommitmentKeyTrait, AccountState, AccountStateCommitment, AccountStateWithoutSk,
};
use crate::auth_proofs::transparent::AuthProofTransparent;
use crate::util::{
    BPProof, bp_gens_for_vec_commitment, enforce_constraints_for_randomness_relations,
    get_verification_tuples_with_rng, handle_verification_tuples, prove_with_rng,
};
use crate::{
    ASSET_ID_LABEL, Error, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_CHALLENGE_LABEL,
    TXN_EVEN_LABEL, TXN_ODD_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript,
    error::Result,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec_divisors::DivisorCurve;
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::io::Write;
use ark_std::string::ToString;
use ark_std::{UniformRand, format, vec, vec::Vec};
use bulletproofs::BulletproofGens;
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, BALANCE_BITS, Balance};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonTransparentWithoutCommitmentsProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub r1cs_proof: Option<BPProof<G0, G1>>,
    pub re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,
    pub comm_bp: Affine<G0>,
    pub t_bp: Affine<G0>,
    pub resp_bp: PartialSchnorrResponse<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>
{
    /// First part of verification: setup verifiers, write public inputs, nullifier T-value,
    /// commit_vec, enforce constraints, BP T-value to transcript.
    ///
    /// Transcript order written: public_inputs, t_null, [commit_vec internal], t_bp.
    /// After this returns, caller gets transcript to add: acc_T_values, [pk_enc], then derives challenge.
    pub fn challenge_contribution_with_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
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
            ASSET_ID_LABEL,
            asset_id,
            AMOUNT_LABEL,
            amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.current_rho_gen();

        self.resp_null
            .challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        let _ = transcript;

        let mut vars = if has_balance_decreased {
            let mut vars = even_verifier.commit_vec(7, self.comm_bp);
            let new_bal_var = vars.pop().unwrap();
            range_proof(even_verifier, new_bal_var.into(), None, BALANCE_BITS.into())?;
            vars
        } else {
            even_verifier.commit_vec(6, self.comm_bp)
        };

        enforce_constraints_for_randomness_relations(even_verifier, &mut vars);

        let mut transcript = even_verifier.transcript();
        self.t_bp.serialize_compressed(&mut transcript)?;

        Ok(())
    }

    /// Verify the partial proof's sigma protocols (nullifier + BP Schnorr).
    pub fn verify_with_given_challenge(
        &self,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        account_tree_params: &SelRerandProofParametersNew<
            G0,
            G1,
            impl DiscreteLogParameters,
            impl DiscreteLogParameters,
        >,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        challenge: &F0,
        resp_acc_old: &SchnorrResponse<Affine<G0>>,
        resp_acc_new: &PartialSchnorrResponse<Affine<G0>>,
        include_sk: bool,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let nullifier_gen = account_comm_key.current_rho_gen();

        // asset_id is revealed so no witness for that but re-randomization (curve tree) is also added.
        // -2 if include_sk is false since 2 items (sk, sk_enc) are not included in the proof
        let expected_len = NUM_GENERATORS - if include_sk { 0 } else { 2 };
        if resp_acc_old.0.len() != expected_len {
            return Err(Error::ProofVerificationError(format!(
                "Invalid resp_acc_old length. Expected {}, got {}",
                expected_len,
                resp_acc_old.0.len()
            )));
        }

        // offset is only 1 since sk_enc is the last witness
        let offset = if include_sk { 0 } else { 1 };

        let nullifier_rho_response = &resp_acc_old.0[4 - offset];

        // Build missing BP responses and verify partial (nullifier + BP)
        let i = 4 - offset;
        let resp_acc_new_rho = resp_acc_new.responses.get(&i).copied().ok_or_else(|| {
            Error::ProofVerificationError(format!("Missing resp_acc_new response for index {i}"))
        })?;
        let i = 6 - offset;
        let resp_acc_new_s = resp_acc_new.responses.get(&i).copied().ok_or_else(|| {
            Error::ProofVerificationError(format!("Missing resp_acc_new response for index {i}"))
        })?;

        let mut missing_resps_bp = BTreeMap::new();
        missing_resps_bp.insert(1, resp_acc_old.0[3 - offset]); // rho
        missing_resps_bp.insert(2, resp_acc_old.0[4 - offset]); // current_rho
        missing_resps_bp.insert(3, resp_acc_new_rho); // new current_rho
        missing_resps_bp.insert(4, resp_acc_old.0[5 - offset]); // randomness
        missing_resps_bp.insert(5, resp_acc_old.0[6 - offset]); // current_randomness
        missing_resps_bp.insert(6, resp_acc_new_s); // new current_randomness
        if has_balance_decreased {
            missing_resps_bp.insert(7, resp_acc_old.0[1 - offset]); // balance
        }

        verify_or_rmc_2!(
            rmc,
            self.resp_null,
            "Nullifier proof verification failed",
            nullifier,
            nullifier_gen,
            challenge,
            nullifier_rho_response,
        );

        let bp_gens_vec = if has_balance_decreased {
            CommonTransparentProof::<L, F0, F1, G0, G1>::bp_gens_vec_bal_decr(
                account_tree_params.even_parameters.bp_gens(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
            )
            .to_vec()
        } else {
            CommonTransparentProof::<L, F0, F1, G0, G1>::bp_gens_vec(
                account_tree_params.even_parameters.bp_gens(),
                account_tree_params.even_parameters.pc_gens().B_blinding,
            )
            .to_vec()
        };

        verify_partial_schnorr_resp_or_rmc!(
            rmc,
            self.resp_bp,
            bp_gens_vec,
            self.comm_bp,
            self.t_bp,
            challenge,
            missing_resps_bp,
        );

        Ok(())
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
struct CommonTransparentProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub without_comms: CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
    t_acc_old: Affine<G0>,
    t_acc_new: Affine<G0>,
    resp_acc_old: SchnorrResponse<Affine<G0>>,
    resp_acc_new: PartialSchnorrResponse<Affine<G0>>,
    resp_eph_pk: Vec<PartialPokDiscreteLog<Affine<G0>>>,
    resp_enc: Partial1PokPedersenCommitment<Affine<G0>>,
    pub encrypted_pubkey: EncryptedPublicKey<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonTransparentProof<L, F0, F1, G0, G1>
{
    fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
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

        let (mut proof, nullifier) = Self::new_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            amount,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            has_balance_decreased,
            auditor_keys,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
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

        proof.without_comms.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((proof, nullifier))
    }

    fn new_with_given_prover<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_same_accounts(account, updated_account, true)?;
        ensure_correct_balance_change(
            account.as_ref_without_sk(),
            updated_account.as_ref_without_sk(),
            amount,
            has_balance_decreased,
        )?;
        ensure_counter_unchanged(
            account.as_ref_without_sk(),
            updated_account.as_ref_without_sk(),
        )?;

        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        let acc_proto = AccountCommitmentsProtocol::init(rng, account_comm_key.clone(), b_blinding);

        let (t_eph_pk, t_enc, encrypted_pubkey) = {
            let mut transcript = even_prover.transcript();
            acc_proto.challenge_contribution(&mut transcript)?;

            let sk_gen = account_comm_key.sk_gen();
            init_pk_enc_protocol(
                rng,
                account.sk,
                acc_proto.sk_blinding,
                auditor_keys.clone(),
                sk_gen,
                enc_key_gen,
                &mut transcript,
            )?
        };

        let (partial_proto, nullifier) =
            CommonTransparentWithoutCommitmentsProtocol::init_with_given_prover::<
                _,
                Parameters0,
                Parameters1,
            >(
                rng,
                amount,
                &account.as_without_sk(),
                &updated_account.as_without_sk(),
                updated_account_commitment,
                leaf_path,
                has_balance_decreased,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                acc_proto.new_balance_blinding,
                acc_proto.initial_rho_blinding,
                acc_proto.old_rho_blinding,
                acc_proto.new_rho_blinding,
                acc_proto.initial_s_blinding,
                acc_proto.old_s_blinding,
                acc_proto.new_s_blinding,
                even_prover,
                odd_prover,
            )?;

        let challenge = {
            let transcript = even_prover.transcript();
            transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL)
        };

        let (resp_acc_old, resp_acc_new, t_acc_old_t, t_acc_new_t) = acc_proto.gen_proof(
            &challenge,
            account.sk,
            updated_account.without_sk.balance.into(),
            account.without_sk.counter.into(),
            account.without_sk.rho,
            account.without_sk.current_rho,
            account.without_sk.randomness,
            account.without_sk.current_randomness,
            account.without_sk.id,
            account.sk_enc,
            partial_proto.rerandomization,
            updated_account.without_sk.current_rho,
            updated_account.without_sk.current_randomness,
        )?;

        let (resp_eph_pk, resp_enc) = reps_pk_enc(t_eph_pk, t_enc, &challenge);

        let partial = partial_proto.gen_proof(&challenge);

        Ok((
            Self {
                without_comms: partial,
                t_acc_old: t_acc_old_t,
                t_acc_new: t_acc_new_t,
                resp_acc_old,
                resp_acc_new,
                resp_enc,
                resp_eph_pk,
                encrypted_pubkey,
            },
            nullifier,
        ))
    }

    fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
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

        let (even_tuple, odd_tuple) = self
            .verify_and_return_tuples::<_, Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                has_balance_decreased,
                auditor_keys,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                enc_key_gen,
                rng,
                rmc_0,
            )?;

        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

        self.verify_sigma_protocols_and_enforce_constraints::<Parameters0, Parameters1>(
            asset_id,
            amount,
            updated_account_commitment,
            nullifier,
            has_balance_decreased,
            auditor_keys,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            &mut even_verifier,
            &mut odd_verifier,
            rmc,
        )?;

        let r1cs_proof = self
            .without_comms
            .r1cs_proof
            .as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof not found".to_string()))?;

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )
    }

    fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        if self.without_comms.resp_bp.responses.len() != 1 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                1,
                self.without_comms.resp_bp.responses.len(),
            ));
        }

        let sk_gen = account_comm_key.sk_gen();
        {
            let mut transcript = even_verifier.transcript();

            self.t_acc_old.serialize_compressed(&mut transcript)?;
            self.t_acc_new.serialize_compressed(&mut transcript)?;

            chal_contrib_pk_enc(
                &self.resp_eph_pk,
                &self.resp_enc,
                &self.encrypted_pubkey,
                &auditor_keys,
                sk_gen,
                enc_key_gen,
                &mut transcript,
            )?;
        }

        self.without_comms
            .challenge_contribution_with_verifier::<Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                has_balance_decreased,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                even_verifier,
                odd_verifier,
            )?;

        let challenge = {
            let transcript = even_verifier.transcript();
            transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL)
        };

        self.without_comms.verify_with_given_challenge(
            nullifier,
            has_balance_decreased,
            account_tree_params,
            account_comm_key.clone(),
            &challenge,
            &self.resp_acc_old,
            &self.resp_acc_new,
            true,
            rmc.as_mut().map(|r| &mut **r),
        )?;

        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;
        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let mut y = self
            .without_comms
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
            - asset_id_comm;
        if has_balance_decreased {
            y = y - (account_comm_key.balance_gen() * F0::from(amount));
        } else {
            y = y + (account_comm_key.balance_gen() * F0::from(amount));
        }

        let y_new = updated_account_commitment.0 - asset_id_comm;

        verify_transparent_acc_comm(
            &self.resp_acc_old,
            &self.resp_acc_new,
            self.t_acc_old,
            self.t_acc_new,
            y.into_affine(),
            y_new.into_affine(),
            account_comm_key.clone(),
            b_blinding,
            true,
            &challenge,
            rmc.as_mut().map(|r| &mut **r),
        )?;

        verify_pk_enc(
            &self.resp_eph_pk,
            &self.resp_enc,
            &self.encrypted_pubkey,
            &auditor_keys,
            &challenge,
            &self.resp_acc_old.0[0],
            sk_gen,
            enc_key_gen,
            rmc.as_mut().map(|r| &mut **r),
        )?;

        Ok(())
    }

    fn bp_gens_vec_bal_decr(
        bp_gens: &BulletproofGens<Affine<G0>>,
        b_blinding: Affine<G0>,
    ) -> [Affine<G0>; 8] {
        let mut gens = bp_gens_for_vec_commitment(7, bp_gens);
        [
            b_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ]
    }

    fn bp_gens_vec(
        bp_gens: &BulletproofGens<Affine<G0>>,
        b_blinding: Affine<G0>,
    ) -> [Affine<G0>; 7] {
        let mut gens = bp_gens_for_vec_commitment(6, bp_gens);
        [
            b_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ]
    }
}

// Split proof types for W2/W3 workflows (Ledger + Host)

/// Host portion of the split account commitment proof without secret key
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountCommitmentsWithoutSkProof<G: SWCurveConfig + Clone + Copy> {
    pub t_acc_old: Affine<G>,
    pub t_acc_new: Affine<G>,
    /// Full response for old leaf: 8 generators
    pub resp_acc_old: SchnorrResponse<Affine<G>>,
    /// Partial response for new account: 3 unique indices (current_rho, current_randomness, B_blinding)
    pub resp_acc_new: PartialSchnorrResponse<Affine<G>>,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsWithoutSkProof<G> {
    /// Verify account commitment Schnorr proofs (without sk/sk_enc).
    pub fn verify_with_given_challenge(
        &self,
        y_old: Affine<G>,
        y_new: Affine<G>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        blinding_gen: Affine<G>,
        challenge: &G::ScalarField,
        rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
    ) -> Result<()> {
        verify_transparent_acc_comm(
            &self.resp_acc_old,
            &self.resp_acc_new,
            self.t_acc_old,
            self.t_acc_new,
            y_old,
            y_new,
            account_comm_key,
            blinding_gen,
            false,
            challenge,
            rmc,
        )
    }
}

/// Combined split proof for account commitments: auth proof (Ledger) + host proof.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct TransparentCommitmentsSplitProof<G: SWCurveConfig + Clone + Copy> {
    pub auth_proof: AuthProofTransparent<Affine<G>>,
    pub host_proof: AccountCommitmentsWithoutSkProof<G>,
}

/// Solo prover-side protocol for account commitment Schnorr proofs (with sk, sk_enc).
/// Creates all blindings internally and stores shared ones for the partial protocol.
#[derive(Clone, Debug)]
pub struct AccountCommitmentsProtocol<G: SWCurveConfig + Clone + Copy> {
    pub t_acc_old: SchnorrCommitment<Affine<G>>,
    pub t_acc_new: SchnorrCommitment<Affine<G>>,
    /// Blindings shared with partial protocol
    pub new_balance_blinding: G::ScalarField,
    pub initial_rho_blinding: G::ScalarField,
    pub old_rho_blinding: G::ScalarField,
    pub new_rho_blinding: G::ScalarField,
    pub initial_s_blinding: G::ScalarField,
    pub old_s_blinding: G::ScalarField,
    pub new_s_blinding: G::ScalarField,
    /// Blindings not shared with partial
    pub sk_blinding: G::ScalarField,
    pub sk_enc_blinding: G::ScalarField,
    pub counter_blinding: G::ScalarField,
    pub id_blinding: G::ScalarField,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsProtocol<G> {
    /// Creates all blindings internally. Shared blindings can be read from struct
    /// and passed to the partial protocol.
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        b_blinding: Affine<G>,
    ) -> Self {
        let sk_blinding = G::ScalarField::rand(rng);
        let sk_enc_blinding = G::ScalarField::rand(rng);
        let (
            t_acc_old,
            t_acc_new,
            new_balance_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_s_blinding,
            old_s_blinding,
            new_s_blinding,
            counter_blinding,
            id_blinding,
        ) = init_transparent_acc_comm(
            rng,
            account_comm_key,
            b_blinding,
            Some(sk_blinding),
            Some(sk_enc_blinding),
        );

        Self {
            t_acc_old,
            t_acc_new,
            new_balance_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_s_blinding,
            old_s_blinding,
            new_s_blinding,
            sk_blinding,
            counter_blinding,
            id_blinding,
            sk_enc_blinding,
        }
    }

    pub fn challenge_contribution<W: Write>(&self, writer: &mut W) -> Result<()> {
        self.t_acc_old.challenge_contribution(&mut *writer)?;
        self.t_acc_new.challenge_contribution(writer)?;
        Ok(())
    }

    /// Generate the solo account commitment proof.
    pub fn gen_proof(
        self,
        challenge: &G::ScalarField,
        sk: G::ScalarField,
        balance: G::ScalarField,
        counter: G::ScalarField,
        initial_rho: G::ScalarField,
        old_acc_rho: G::ScalarField,
        initial_randomness: G::ScalarField,
        old_acc_randomness: G::ScalarField,
        id: G::ScalarField,
        sk_enc: G::ScalarField,
        rerandomization: G::ScalarField,
        new_acc_rho: G::ScalarField,
        new_acc_randomness: G::ScalarField,
    ) -> Result<(
        SchnorrResponse<Affine<G>>,
        PartialSchnorrResponse<Affine<G>>,
        Affine<G>,
        Affine<G>,
    )> {
        let (resp_acc_old, resp_acc_new) = resp_transparent_acc_comm(
            &self.t_acc_old,
            &self.t_acc_new,
            challenge,
            Some(sk),
            Some(sk_enc),
            balance,
            counter,
            initial_rho,
            old_acc_rho,
            initial_randomness,
            old_acc_randomness,
            id,
            rerandomization,
            new_acc_rho,
            new_acc_randomness,
            None, // solo mode: no B_blinding in new commitment
        )?;
        Ok((
            resp_acc_old,
            resp_acc_new,
            self.t_acc_old.t,
            self.t_acc_new.t,
        ))
    }
}

/// Prover-side protocol state for host's account commitment Schnorr proofs, without secret keys.
/// Creates all blindings internally. Shared blindings can be read from struct.
#[derive(Clone, Debug)]
pub struct AccountCommitmentsWithoutSkProtocol<G: SWCurveConfig + Clone + Copy> {
    pub t_acc_old: SchnorrCommitment<Affine<G>>,
    pub t_acc_new: SchnorrCommitment<Affine<G>>,
    /// Blindings shared with partial protocol
    pub new_balance_blinding: G::ScalarField,
    pub initial_rho_blinding: G::ScalarField,
    pub old_rho_blinding: G::ScalarField,
    pub new_rho_blinding: G::ScalarField,
    pub initial_s_blinding: G::ScalarField,
    pub old_s_blinding: G::ScalarField,
    pub new_s_blinding: G::ScalarField,
    /// Blindings not shared with partial
    pub counter_blinding: G::ScalarField,
    pub id_blinding: G::ScalarField,
    /// Random values for splitting commitment with auth proof.
    /// Auth proves `B_blinding * rand_part_old_comm` in old commitment and `B_blinding * rand_new_comm` in new.
    /// Host proves `B_blinding * (rerand - rand_part_old_comm)` in old and `B_blinding * (-rand_new_comm)` in new.
    pub rand_part_old_comm: G::ScalarField,
    pub rand_new_comm: G::ScalarField,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsWithoutSkProtocol<G> {
    /// Creates all blindings internally. Shared blindings (`new_balance_blinding`,
    /// `initial_rho_blinding`, `old_rho_blinding`, `new_rho_blinding`, `initial_s_blinding`,
    /// `old_s_blinding`) can be read from the struct and passed to the partial protocol.
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        b_blinding: Affine<G>,
    ) -> Self {
        let (
            t_acc_old,
            t_acc_new,
            new_balance_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_s_blinding,
            old_s_blinding,
            new_s_blinding,
            counter_blinding,
            id_blinding,
        ) = init_transparent_acc_comm(rng, account_comm_key, b_blinding, None, None);

        let rand_part_old_comm = G::ScalarField::rand(rng);
        let rand_new_comm = G::ScalarField::rand(rng);

        Self {
            t_acc_old,
            t_acc_new,
            new_balance_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_s_blinding,
            old_s_blinding,
            new_s_blinding,
            counter_blinding,
            id_blinding,
            rand_part_old_comm,
            rand_new_comm,
        }
    }

    /// Generate the host's portion of the split proof.
    /// Takes the full `rerandomization` value; computes the host's share internally.
    pub fn gen_proof(
        self,
        challenge: &G::ScalarField,
        balance: G::ScalarField,
        counter: G::ScalarField,
        rho: G::ScalarField,
        current_rho: G::ScalarField,
        randomness: G::ScalarField,
        current_randomness: G::ScalarField,
        id: G::ScalarField,
        rerandomization: G::ScalarField,
        new_current_rho: G::ScalarField,
        new_current_randomness: G::ScalarField,
    ) -> Result<AccountCommitmentsWithoutSkProof<G>> {
        let host_rerandomization = rerandomization - self.rand_part_old_comm;
        let (resp_acc_old, resp_acc_new) = resp_transparent_acc_comm(
            &self.t_acc_old,
            &self.t_acc_new,
            challenge,
            None,
            None,
            balance,
            counter,
            rho,
            current_rho,
            randomness,
            current_randomness,
            id,
            host_rerandomization,
            new_current_rho,
            new_current_randomness,
            Some(-self.rand_new_comm), // host mode: B_blinding witness for new commitment
        )?;
        Ok(AccountCommitmentsWithoutSkProof {
            t_acc_old: self.t_acc_old.t,
            t_acc_new: self.t_acc_new.t,
            resp_acc_old,
            resp_acc_new,
        })
    }
}

/// Prover-side protocol state for host's partial transparent proof.
pub struct CommonTransparentWithoutCommitmentsProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub t_null: PokDiscreteLogProtocol<Affine<G0>>,
    pub t_bp: SchnorrCommitment<Affine<G0>>,
    pub re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    pub rerandomization: F0,
    pub comm_bp: Affine<G0>,
    pub comm_bp_blinding: F0,
    pub has_balance_decreased: bool,
    pub old_account: AccountStateWithoutSk<Affine<G0>>,
    pub updated_account: AccountStateWithoutSk<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonTransparentWithoutCommitmentsProtocol<L, F0, F1, G0, G1>
{
    /// Initialize the partial protocol: curve-tree re-randomization, transcript setup,
    /// nullifier T-value, BP commitment + constraints, BP T-value contribution.
    pub fn init_with_given_prover<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        has_balance_decreased: bool,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        // All blindings shared between account commitment and BP Schnorr protocols
        new_balance_blinding: F0,
        initial_rho_blinding: F0,
        old_rho_blinding: F0,
        new_rho_blinding: F0,
        initial_s_blinding: F0,
        old_s_blinding: F0,
        new_s_blinding: F0,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_same_accounts_without_sk(account, updated_account, true)?;
        ensure_correct_balance_change(account, updated_account, amount, has_balance_decreased)?;
        ensure_counter_unchanged(account, updated_account)?;

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
            ASSET_ID_LABEL,
            account.asset_id,
            AMOUNT_LABEL,
            amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.current_rho_gen();
        let nullifier = account.nullifier(&account_comm_key);

        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, old_rho_blinding, &nullifier_gen);

        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        let _ = transcript;

        let comm_bp_blinding = F0::rand(rng);
        let (comm_bp, mut vars) = if has_balance_decreased {
            let (comm_bp, mut vars) = even_prover.commit_vec(
                &[
                    account.rho,
                    account.current_rho,
                    updated_account.current_rho,
                    account.randomness,
                    account.current_randomness,
                    updated_account.current_randomness,
                    updated_account.balance.into(),
                ],
                comm_bp_blinding,
                &account_tree_params.even_parameters.bp_gens(),
            );
            let new_bal_var = vars.pop().unwrap();
            range_proof(
                even_prover,
                new_bal_var.into(),
                Some(updated_account.balance.into()),
                BALANCE_BITS.into(),
            )?;
            (comm_bp, vars)
        } else {
            even_prover.commit_vec(
                &[
                    account.rho,
                    account.current_rho,
                    updated_account.current_rho,
                    account.randomness,
                    account.current_randomness,
                    updated_account.current_randomness,
                ],
                comm_bp_blinding,
                &account_tree_params.even_parameters.bp_gens(),
            )
        };
        enforce_constraints_for_randomness_relations(even_prover, &mut vars);

        let t_bp = if has_balance_decreased {
            SchnorrCommitment::new(
                &CommonTransparentProof::<L, F0, F1, G0, G1>::bp_gens_vec_bal_decr(
                    account_tree_params.even_parameters.bp_gens(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
                ),
                vec![
                    F0::rand(rng),
                    initial_rho_blinding,
                    old_rho_blinding,
                    new_rho_blinding,
                    initial_s_blinding,
                    old_s_blinding,
                    new_s_blinding,
                    new_balance_blinding,
                ],
            )
        } else {
            SchnorrCommitment::new(
                &CommonTransparentProof::<L, F0, F1, G0, G1>::bp_gens_vec(
                    account_tree_params.even_parameters.bp_gens(),
                    account_tree_params.even_parameters.pc_gens().B_blinding,
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
            )
        };

        let mut transcript = even_prover.transcript();
        t_bp.challenge_contribution(&mut transcript)?;

        Ok((
            Self {
                t_null,
                t_bp,
                re_randomized_path,
                rerandomization,
                comm_bp,
                comm_bp_blinding,
                has_balance_decreased,
                old_account: account.clone(),
                updated_account: updated_account.clone(),
            },
            nullifier,
        ))
    }

    /// Generate the partial proof given the challenge.
    pub fn gen_proof(
        self,
        challenge: &F0,
    ) -> CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1> {
        let resp_null = self.t_null.gen_partial_proof();
        let mut w = BTreeMap::new();
        w.insert(0, self.comm_bp_blinding);
        let resp_bp = self.t_bp.partial_response(w, challenge).unwrap();

        CommonTransparentWithoutCommitmentsProof {
            r1cs_proof: None,
            re_randomized_path: self.re_randomized_path,
            resp_null,
            comm_bp: self.comm_bp,
            t_bp: self.t_bp.t,
            resp_bp,
        }
    }
}

/// The full split proof: partial (host) + split commitment proof (auth + host).
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonTransparentSplitProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub partial: CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
    pub commitment_proof: TransparentCommitmentsSplitProof<G0>,
}

/// Prover-side protocol state for the host in the split (W2/W3) transparent flow.
/// init() returns (Self, Prover, Prover, nullifier). Caller derives challenge externally.
/// gen_proof(challenge) consumes Self and provers.
pub struct CommonTransparentSplitProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    acc_host_proto: AccountCommitmentsWithoutSkProtocol<G0>,
    partial_proto: CommonTransparentWithoutCommitmentsProtocol<L, F0, F1, G0, G1>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonTransparentSplitProtocol<L, F0, F1, G0, G1>
{
    /// Initialize the split protocol: creates provers, host commitment protocol, partial protocol.
    /// Returns (protocol, even_prover, odd_prover, nullifier).
    /// The caller should derive the challenge from `even_prover.transcript()` after this returns,
    /// then pass it to `gen_proof`.
    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        has_balance_decreased: bool,
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
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens(),
            even_transcript,
        );
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.pc_gens(),
            odd_transcript,
        );

        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        // Create host account commitment protocol (creates all blindings internally)
        let acc_host_proto =
            AccountCommitmentsWithoutSkProtocol::init(rng, account_comm_key.clone(), b_blinding);

        // Create partial protocol, passing the shared blindings from acc_host_proto
        let (partial_proto, nullifier) =
            CommonTransparentWithoutCommitmentsProtocol::init_with_given_prover::<
                _,
                Parameters0,
                Parameters1,
            >(
                rng,
                amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                has_balance_decreased,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                acc_host_proto.new_balance_blinding,
                acc_host_proto.initial_rho_blinding,
                acc_host_proto.old_rho_blinding,
                acc_host_proto.new_rho_blinding,
                acc_host_proto.initial_s_blinding,
                acc_host_proto.old_s_blinding,
                acc_host_proto.new_s_blinding,
                &mut even_prover,
                &mut odd_prover,
            )?;

        let host_rerandomization =
            partial_proto.rerandomization - acc_host_proto.rand_part_old_comm;

        {
            let mut transcript = even_prover.transcript();
            acc_host_proto
                .t_acc_old
                .challenge_contribution(&mut transcript)?;
            acc_host_proto
                .t_acc_new
                .challenge_contribution(&mut transcript)?;

            let acc_old = <Projective<G0> as VariableBaseMSM>::msm_unchecked(
                &acc_old_gens_host(&account_comm_key, b_blinding),
                &[
                    F0::from(updated_account.balance),
                    account.counter.into(),
                    account.rho,
                    account.current_rho,
                    account.randomness,
                    account.current_randomness,
                    account.id,
                    host_rerandomization,
                ],
            )
            .into_affine();
            let acc_new = <Projective<G0> as VariableBaseMSM>::msm_unchecked(
                &acc_new_gens_host(&account_comm_key, b_blinding),
                &[
                    F0::from(updated_account.balance),
                    account.counter.into(),
                    account.rho,
                    updated_account.current_rho,
                    account.randomness,
                    updated_account.current_randomness,
                    account.id,
                    -acc_host_proto.rand_new_comm,
                ],
            )
            .into_affine();

            #[cfg(not(feature = "ignore_prover_input_sanitation"))]
            if cfg!(debug_assertions) {
                // Cross-check: acc_old - acc_new should equal the contribution of the
                // fields that differ (current_rho, current_randomness, B_blinding term).
                debug_assert_eq!(
                    (acc_old.into_group() - acc_new.into_group()).into_affine(),
                    <Projective<G0> as VariableBaseMSM>::msm_unchecked(
                        &[
                            account_comm_key.current_rho_gen(),
                            account_comm_key.current_randomness_gen(),
                            b_blinding,
                        ],
                        &[
                            account.current_rho - updated_account.current_rho,
                            account.current_randomness - updated_account.current_randomness,
                            host_rerandomization + acc_host_proto.rand_new_comm,
                        ],
                    )
                    .into_affine()
                );
            }

            acc_old.serialize_compressed(&mut transcript)?;
            acc_new.serialize_compressed(&mut transcript)?;
        }

        Ok((
            Self {
                acc_host_proto,
                partial_proto,
            },
            even_prover,
            odd_prover,
            nullifier,
        ))
    }

    /// Returns the rerandomized leaf point (needed by the auth proof).
    pub fn rerandomized_leaf(&self) -> Affine<G0> {
        self.partial_proto
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
    }

    /// Returns the `rand_part_old_comm` value (needed by `AuthProofTransparent::new`).
    pub fn rand_part_old_comm(&self) -> F0 {
        self.acc_host_proto.rand_part_old_comm
    }

    /// Returns the `rand_new_comm` value (needed by `AuthProofTransparent::new`).
    pub fn rand_new_comm(&self) -> F0 {
        self.acc_host_proto.rand_new_comm
    }

    /// Generate the host's partial proof and commitment proof, consuming the protocol.
    /// `challenge` is derived externally by the caller from the transcript after `init`.
    /// Returns (partial, host_commitment_proof).
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
        CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        AccountCommitmentsWithoutSkProof<G0>,
    )> {
        let host_commitment_proof = self.acc_host_proto.gen_proof(
            challenge,
            F0::from(self.partial_proto.updated_account.balance),
            self.partial_proto.old_account.counter.into(),
            self.partial_proto.old_account.rho,
            self.partial_proto.old_account.current_rho,
            self.partial_proto.old_account.randomness,
            self.partial_proto.old_account.current_randomness,
            self.partial_proto.old_account.id,
            self.partial_proto.rerandomization,
            self.partial_proto.updated_account.current_rho,
            self.partial_proto.updated_account.current_randomness,
        )?;

        let mut partial = self.partial_proto.gen_proof(challenge);

        // Finalize Bulletproof
        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((partial, host_commitment_proof))
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonTransparentSplitProof<L, F0, F1, G0, G1>
{
    /// Phase 1: Set up verifier transcripts, write challenge contributions (host commitment T-values,
    /// re-randomization, public inputs, nullifier, BP), and derive the challenge.
    /// Returns `(even_verifier, odd_verifier, challenge_h)`.
    pub fn challenge_contribution<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
        F0,
    )> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

        // Shared verification setup (re-rand, public_inputs, t_null, commit_vec, t_bp)
        self.partial
            .challenge_contribution_with_verifier::<Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                has_balance_decreased,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                &mut even_verifier,
                &mut odd_verifier,
            )?;

        let mut transcript = even_verifier.transcript();

        // Host account commitment T-values and Y-values together
        self.commitment_proof
            .host_proof
            .t_acc_old
            .serialize_compressed(&mut transcript)?;
        self.commitment_proof
            .host_proof
            .t_acc_new
            .serialize_compressed(&mut transcript)?;

        let (y_old, y_new) = self.old_and_new_host_commitments(
            asset_id,
            amount,
            has_balance_decreased,
            updated_account_commitment,
            account_comm_key.asset_id_gen(),
            account_comm_key.balance_gen(),
        );
        y_old.serialize_compressed(&mut transcript)?;
        y_new.serialize_compressed(&mut transcript)?;

        let challenge_h = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        Ok((even_verifier, odd_verifier, challenge_h))
    }

    /// Phase 2: Verify sigma protocols (nullifier, BP, Schnorr) and R1CS proof
    /// using the given challenge and verifier state from `challenge_contribution`.
    /// Returns `(even_tuple, odd_tuple)`.
    pub fn verify_host_and_return_tuples_with_challenge<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        challenge: &F0,
        even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        if self.partial.resp_bp.responses.len() != 1 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                1,
                self.partial.resp_bp.responses.len(),
            ));
        }

        // Compute verification points for host account commitments
        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        let (y_old_affine, y_new_affine) = self.old_and_new_host_commitments(
            asset_id,
            amount,
            has_balance_decreased,
            updated_account_commitment,
            account_comm_key.asset_id_gen(),
            account_comm_key.balance_gen(),
        );

        self.partial.verify_with_given_challenge(
            nullifier,
            has_balance_decreased,
            account_tree_params,
            account_comm_key.clone(),
            challenge,
            &self.commitment_proof.host_proof.resp_acc_old,
            &self.commitment_proof.host_proof.resp_acc_new,
            false,
            rmc.as_deref_mut(),
        )?;

        // Verify host account commitment proofs
        self.commitment_proof
            .host_proof
            .verify_with_given_challenge(
                y_old_affine,
                y_new_affine,
                account_comm_key,
                b_blinding,
                challenge,
                rmc,
            )?;

        let r1cs_proof =
            self.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        let (even_tuple, odd_tuple) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )?;

        Ok((even_tuple, odd_tuple))
    }

    pub fn verify_host_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(
        VerificationTuple<Affine<G0>>,
        VerificationTuple<Affine<G1>>,
        F0,
    )> {
        let (even_verifier, odd_verifier, challenge_h) = self
            .challenge_contribution::<Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                has_balance_decreased,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
            )?;

        let (even_tuple, odd_tuple) = self
            .verify_host_and_return_tuples_with_challenge::<_, Parameters0, Parameters1>(
                &challenge_h,
                even_verifier,
                odd_verifier,
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                has_balance_decreased,
                account_tree_params,
                account_comm_key,
                rng,
                rmc,
            )?;

        Ok((even_tuple, odd_tuple, challenge_h))
    }

    /// verify sigma protocols and R1CS, then handle tuples.
    /// Takes `(even_verifier, odd_verifier, challenge)` from `challenge_contribution`.
    pub fn verify_host_with_challenge<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        challenge: &F0,
        even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
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
        let (even_tuple, odd_tuple) = self
            .verify_host_and_return_tuples_with_challenge::<_, Parameters0, Parameters1>(
                challenge,
                even_verifier,
                odd_verifier,
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                has_balance_decreased,
                account_tree_params,
                account_comm_key,
                rng,
                rmc_0,
            )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    /// complete host verification from scratch.
    /// Returns the derived challenge for use in auth-proof coordination.
    pub fn verify_host<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<F0> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple, challenge_h) = self
            .verify_host_and_return_tuples::<_, Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                has_balance_decreased,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                rng,
                rmc_0,
            )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)?;
        Ok(challenge_h)
    }

    fn old_and_new_host_commitments(
        &self,
        asset_id: AssetId,
        amount: Balance,
        has_balance_decreased: bool,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        asset_id_gen: Affine<G0>,
        balance_gen: Affine<G0>,
    ) -> (Affine<G0>, Affine<G0>) {
        let asset_id_comm = (asset_id_gen * F0::from(asset_id)).into_affine();
        let mut y_old = self
            .partial
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
            .into_group()
            - asset_id_comm;
        if has_balance_decreased {
            y_old -= balance_gen * F0::from(amount);
        } else {
            y_old += balance_gen * F0::from(amount);
        }
        y_old -= self
            .commitment_proof
            .auth_proof
            .partial_re_randomized_account_commitment;
        let y_old = y_old.into_affine();

        let y_new = (updated_account_commitment.0.into_group()
            - asset_id_comm
            - self
                .commitment_proof
                .auth_proof
                .partial_updated_account_commitment)
            .into_affine();
        (y_old, y_new)
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct WithdrawSplitProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(pub CommonTransparentSplitProof<L, F0, F1, G0, G1>);

/// Prover-side protocol state for the host in the W2/W3 withdraw (split transparent) flow.
/// Wraps `CommonTransparentSplitProtocol` with `has_balance_decreased` hardcoded to `true`.
/// `gen_proof` assembles and returns a complete `WithdrawSplitProof`.
pub struct WithdrawSplitProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(CommonTransparentSplitProtocol<L, F0, F1, G0, G1>);

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> WithdrawSplitProtocol<L, F0, F1, G0, G1>
{
    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account: &AccountStateWithoutSk<Affine<G0>>,
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
        let (proto, ep, op, nullifier) =
            CommonTransparentSplitProtocol::init::<_, Parameters0, Parameters1>(
                rng,
                amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                true,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;
        Ok((Self(proto), ep, op, nullifier))
    }

    pub fn rerandomized_leaf(&self) -> Affine<G0> {
        self.0.rerandomized_leaf()
    }

    pub fn rand_part_old_comm(&self) -> F0 {
        self.0.rand_part_old_comm()
    }

    pub fn rand_new_comm(&self) -> F0 {
        self.0.rand_new_comm()
    }

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
        CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        AccountCommitmentsWithoutSkProof<G0>,
    )> {
        self.0.gen_proof::<_, Parameters0, Parameters1>(
            challenge,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )
    }

    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        AccountCommitmentsWithoutSkProof<G0>,
        Affine<G0>,
        F0,
        F0,
        Affine<G0>,
    )> {
        let (protocol, mut even_prover, odd_prover, nullifier) =
            Self::init::<_, Parameters0, Parameters1>(
                rng,
                amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;
        let rerandomized_leaf = protocol.rerandomized_leaf();
        let rand_part_old_comm = protocol.rand_part_old_comm();
        let rand_new_comm = protocol.rand_new_comm();
        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        let (partial, host_proof) = protocol.gen_proof::<_, Parameters0, Parameters1>(
            &challenge_h,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )?;
        Ok((
            partial,
            host_proof,
            rerandomized_leaf,
            rand_part_old_comm,
            rand_new_comm,
            nullifier,
        ))
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DepositSplitProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(pub CommonTransparentSplitProof<L, F0, F1, G0, G1>);

/// Prover-side protocol state for the host in the W2/W3 deposit (split transparent) flow.
/// Wraps `CommonTransparentSplitProtocol` with `has_balance_decreased` hardcoded to `false`.
/// `gen_proof` assembles and returns a complete `DepositSplitProof`.
pub struct DepositSplitProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(CommonTransparentSplitProtocol<L, F0, F1, G0, G1>);

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> DepositSplitProtocol<L, F0, F1, G0, G1>
{
    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account: &AccountStateWithoutSk<Affine<G0>>,
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
        let (proto, ep, op, nullifier) =
            CommonTransparentSplitProtocol::init::<_, Parameters0, Parameters1>(
                rng,
                amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                false,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;
        Ok((Self(proto), ep, op, nullifier))
    }

    pub fn rerandomized_leaf(&self) -> Affine<G0> {
        self.0.rerandomized_leaf()
    }

    pub fn rand_part_old_comm(&self) -> F0 {
        self.0.rand_part_old_comm()
    }

    pub fn rand_new_comm(&self) -> F0 {
        self.0.rand_new_comm()
    }

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
        CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        AccountCommitmentsWithoutSkProof<G0>,
    )> {
        self.0.gen_proof::<_, Parameters0, Parameters1>(
            challenge,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )
    }

    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account: &AccountStateWithoutSk<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        CommonTransparentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        AccountCommitmentsWithoutSkProof<G0>,
        Affine<G0>,
        F0,
        F0,
        Affine<G0>,
    )> {
        let (protocol, mut even_prover, odd_prover, nullifier) =
            Self::init::<_, Parameters0, Parameters1>(
                rng,
                amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;
        let rerandomized_leaf = protocol.rerandomized_leaf();
        let rand_part_old_comm = protocol.rand_part_old_comm();
        let rand_new_comm = protocol.rand_new_comm();
        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        let (partial, host_proof) = protocol.gen_proof::<_, Parameters0, Parameters1>(
            &challenge_h,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )?;
        Ok((
            partial,
            host_proof,
            rerandomized_leaf,
            rand_part_old_comm,
            rand_new_comm,
            nullifier,
        ))
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct WithdrawProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(CommonTransparentProof<L, F0, F1, G0, G1>);

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> WithdrawProof<L, F0, F1, G0, G1>
{
    /// `auditor_keys` is the list auditor/mediator keys for which encryption of account public key is done
    /// `nonce` should include all the relevant information including the "transparent public key"
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) = CommonTransparentProof::new::<_, Parameters0, Parameters1>(
            rng,
            amount,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            true,
            auditor_keys,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
        )?;

        Ok((Self(common), nullifier))
    }

    pub fn new_with_given_prover<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) =
            CommonTransparentProof::new_with_given_prover::<_, Parameters0, Parameters1>(
                rng,
                amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                true,
                auditor_keys,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                enc_key_gen,
                even_prover,
                odd_prover,
            )?;

        Ok((Self(common), nullifier))
    }

    /// `auditor_keys` is the list auditor/mediator keys for which encryption of account public key is done
    /// `nonce` should include all the relevant information including the "transparent public key"
    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        self.0.verify::<_, Parameters0, Parameters1>(
            asset_id,
            amount,
            updated_account_commitment,
            nullifier,
            true,
            auditor_keys,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            rng,
            rmc,
        )
    }

    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        self.0
            .verify_and_return_tuples::<_, Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                true,
                auditor_keys,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                enc_key_gen,
                rng,
                rmc,
            )
    }

    pub fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        self.0
            .verify_sigma_protocols_and_enforce_constraints::<Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                true,
                auditor_keys,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                enc_key_gen,
                even_verifier,
                odd_verifier,
                rmc,
            )
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DepositProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(CommonTransparentProof<L, F0, F1, G0, G1>);

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> DepositProof<L, F0, F1, G0, G1>
{
    /// `auditor_keys` is the list auditor/mediator keys for which encryption of account public key is done
    /// `nonce` should include all the relevant information including the "transparent public key"
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) = CommonTransparentProof::new::<_, Parameters0, Parameters1>(
            rng,
            amount,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            false,
            auditor_keys,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
        )?;

        Ok((Self(common), nullifier))
    }

    pub fn new_with_given_prover<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) =
            CommonTransparentProof::new_with_given_prover::<_, Parameters0, Parameters1>(
                rng,
                amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                false,
                auditor_keys,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                enc_key_gen,
                even_prover,
                odd_prover,
            )?;

        Ok((Self(common), nullifier))
    }

    /// `auditor_keys` is the list auditor/mediator keys for which encryption of account public key is done
    /// `nonce` should include all the relevant information including the "transparent public key"
    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        self.0.verify::<_, Parameters0, Parameters1>(
            asset_id,
            amount,
            updated_account_commitment,
            nullifier,
            false,
            auditor_keys,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            rng,
            rmc,
        )
    }

    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        self.0
            .verify_and_return_tuples::<_, Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                false,
                auditor_keys,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                enc_key_gen,
                rng,
                rmc,
            )
    }

    pub fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        self.0
            .verify_sigma_protocols_and_enforce_constraints::<Parameters0, Parameters1>(
                asset_id,
                amount,
                updated_account_commitment,
                nullifier,
                false,
                auditor_keys,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                enc_key_gen,
                even_verifier,
                odd_verifier,
                rmc,
            )
    }
}

pub fn ensure_counter_unchanged<G>(
    old_state: &AccountStateWithoutSk<G>,
    new_state: &AccountStateWithoutSk<G>,
) -> Result<()>
where
    G: AffineRepr,
{
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if old_state.counter != new_state.counter {
            return Err(Error::ProofGenerationError(
                "Counter must remain unchanged for transparent proofs".to_string(),
            ));
        }
        Ok(())
    }
}

/// Create SchnorrCommitments for transparent account commitment Schnorr proofs.
fn init_transparent_acc_comm<R: CryptoRngCore, G: SWCurveConfig + Clone + Copy>(
    rng: &mut R,
    account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
    b_blinding: Affine<G>,
    sk_blinding: Option<G::ScalarField>,
    sk_enc_blinding: Option<G::ScalarField>,
) -> (
    SchnorrCommitment<Affine<G>>,
    SchnorrCommitment<Affine<G>>,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
) {
    let new_balance_blinding = G::ScalarField::rand(rng);
    let initial_rho_blinding = G::ScalarField::rand(rng);
    let old_rho_blinding = G::ScalarField::rand(rng);
    let new_rho_blinding = G::ScalarField::rand(rng);
    let initial_s_blinding = G::ScalarField::rand(rng);
    let old_s_blinding = G::ScalarField::rand(rng);
    let new_s_blinding = G::ScalarField::rand(rng);
    let counter_blinding = G::ScalarField::rand(rng);
    let id_blinding = G::ScalarField::rand(rng);

    let include_sk = sk_blinding.is_some();

    let mut old_gens = Vec::new();
    let mut old_blindings = Vec::new();
    let mut new_gens = Vec::new();
    let mut new_blindings = Vec::new();

    if let Some(sk_b) = sk_blinding {
        old_gens.push(account_comm_key.sk_gen());
        old_blindings.push(sk_b);
        new_gens.push(account_comm_key.sk_gen());
        new_blindings.push(sk_b);
    }

    old_gens.extend_from_slice(&[
        account_comm_key.balance_gen(),
        account_comm_key.counter_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.current_rho_gen(),
        account_comm_key.randomness_gen(),
        account_comm_key.current_randomness_gen(),
        account_comm_key.id_gen(),
    ]);
    old_blindings.extend_from_slice(&[
        new_balance_blinding,
        counter_blinding,
        initial_rho_blinding,
        old_rho_blinding,
        initial_s_blinding,
        old_s_blinding,
        id_blinding,
    ]);

    if let Some(sk_enc_b) = sk_enc_blinding {
        old_gens.push(account_comm_key.sk_enc_gen());
        old_blindings.push(sk_enc_b);
    }

    old_gens.push(b_blinding);
    old_blindings.push(G::ScalarField::rand(rng));

    // New generators and blindings
    new_gens.extend_from_slice(&[
        account_comm_key.balance_gen(),
        account_comm_key.counter_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.current_rho_gen(),
        account_comm_key.randomness_gen(),
        account_comm_key.current_randomness_gen(),
        account_comm_key.id_gen(),
    ]);
    new_blindings.extend_from_slice(&[
        new_balance_blinding,
        counter_blinding,
        initial_rho_blinding,
        new_rho_blinding,
        initial_s_blinding,
        new_s_blinding,
        id_blinding,
    ]);

    if let Some(sk_enc_b) = sk_enc_blinding {
        new_gens.push(account_comm_key.sk_enc_gen());
        new_blindings.push(sk_enc_b);
    }

    // In host mode (no sk), new commitment also includes B_blinding
    // for the `-rand_new_comm` term that cancels with auth's `B * rand_new_comm`.
    if !include_sk {
        new_gens.push(b_blinding);
        new_blindings.push(G::ScalarField::rand(rng));
    }

    let t_acc_old = SchnorrCommitment::new(&old_gens, old_blindings);
    let t_acc_new = SchnorrCommitment::new(&new_gens, new_blindings);

    (
        t_acc_old,
        t_acc_new,
        new_balance_blinding,
        initial_rho_blinding,
        old_rho_blinding,
        new_rho_blinding,
        initial_s_blinding,
        old_s_blinding,
        new_s_blinding,
        counter_blinding,
        id_blinding,
    )
}

/// Responses for transparent account commitment Schnorr proofs.
/// `new_b_blinding_witness`: in host (split) mode, the witness for B_blinding in the new
/// commitment (i.e., `-rand_new_comm`). Pass `None` for solo mode.
fn resp_transparent_acc_comm<G: SWCurveConfig + Clone + Copy>(
    t_acc_old: &SchnorrCommitment<Affine<G>>,
    t_acc_new: &SchnorrCommitment<Affine<G>>,
    challenge: &G::ScalarField,
    sk: Option<G::ScalarField>,
    sk_enc: Option<G::ScalarField>,
    balance: G::ScalarField,
    counter: G::ScalarField,
    initial_rho: G::ScalarField,
    old_acc_rho: G::ScalarField,
    initial_randomness: G::ScalarField,
    old_acc_randomness: G::ScalarField,
    id: G::ScalarField,
    rerandomization: G::ScalarField,
    new_acc_rho: G::ScalarField,
    new_acc_randomness: G::ScalarField,
    new_b_blinding_witness: Option<G::ScalarField>,
) -> Result<(
    SchnorrResponse<Affine<G>>,
    PartialSchnorrResponse<Affine<G>>,
)> {
    let mut old_wits = Vec::new();
    let offset = if let Some(sk_val) = sk {
        old_wits.push(sk_val);
        0
    } else {
        1
    };
    old_wits.extend_from_slice(&[
        balance,
        counter,
        initial_rho,
        old_acc_rho,
        initial_randomness,
        old_acc_randomness,
        id,
    ]);
    if let Some(sk_enc_val) = sk_enc {
        old_wits.push(sk_enc_val);
    }
    old_wits.push(rerandomization);

    let resp_acc_old = t_acc_old.response(&old_wits, challenge)?;

    let current_rho_idx = CURRENT_RHO_GEN_INDEX - 1 - offset; // -1 since asset-id not present
    let current_randomness_idx = CURRENT_RANDOMNESS_GEN_INDEX - 1 - offset;
    let mut new_wits = BTreeMap::new();
    new_wits.insert(current_rho_idx, new_acc_rho);
    new_wits.insert(current_randomness_idx, new_acc_randomness);
    // In host mode, B_blinding witness (-rand_new_comm) is unique to the new commitment
    if let Some(b_w) = new_b_blinding_witness {
        let b_blinding_idx = 7;
        new_wits.insert(b_blinding_idx, b_w);
    }
    let resp_acc_new = t_acc_new.partial_response(new_wits, challenge)?;

    Ok((resp_acc_old, resp_acc_new))
}

/// verify transparent account commitment Schnorr proofs (old + new).
/// When `include_sk` is true, uses with-sk generators and shares sk, sk_enc, and common fields;
/// otherwise uses without-sk generators and shares only common fields.
fn verify_transparent_acc_comm<G: SWCurveConfig + Clone + Copy>(
    resp_acc_old: &SchnorrResponse<Affine<G>>,
    resp_acc_new: &PartialSchnorrResponse<Affine<G>>,
    t_acc_old: Affine<G>,
    t_acc_new: Affine<G>,
    y_old: Affine<G>,
    y_new: Affine<G>,
    account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
    blinding_gen: Affine<G>,
    include_sk: bool,
    challenge: &G::ScalarField,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
) -> Result<()> {
    let expected_old = if include_sk {
        NUM_GENERATORS
    } else {
        NUM_GENERATORS - 2
    };
    if resp_acc_old.len() != expected_old {
        return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
            expected_old,
            resp_acc_old.len(),
        ));
    }
    // Host mode has 3 partial responses (curr_rho, curr_rand, B_blinding),
    // solo mode has 2 (curr_rho, curr_rand).
    let expected_new = if include_sk { 2 } else { 3 };
    if resp_acc_new.responses.len() != expected_new {
        return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
            expected_new,
            resp_acc_new.responses.len(),
        ));
    }

    let (old_gens, new_gens) = if include_sk {
        (
            acc_old_gens(&account_comm_key, blinding_gen).to_vec(),
            acc_new_gens(&account_comm_key).to_vec(),
        )
    } else {
        // Host mode: new gens also include B_blinding (for -rand_new_comm term)
        (
            acc_old_gens_host(&account_comm_key, blinding_gen).to_vec(),
            acc_new_gens_host(&account_comm_key, blinding_gen).to_vec(),
        )
    };

    verify_schnorr_resp_or_rmc!(rmc, resp_acc_old, old_gens, y_old, t_acc_old, challenge);

    let offset = if include_sk { 1 } else { 0 };

    // Build missing responses for new commitment (shared from old)
    let mut missing_resps = BTreeMap::new();
    if include_sk {
        missing_resps.insert(0, resp_acc_old.0[0]); // sk
    }
    // Common middle: balance, counter, rho, current_rho, randomness, current_randomness, id
    // Share all except current_rho (offset+3) and current_randomness (offset+5)
    missing_resps.insert(offset, resp_acc_old.0[offset]); // balance
    missing_resps.insert(offset + 1, resp_acc_old.0[offset + 1]); // counter
    missing_resps.insert(offset + 2, resp_acc_old.0[offset + 2]); // rho
    missing_resps.insert(offset + 4, resp_acc_old.0[offset + 4]); // randomness
    missing_resps.insert(offset + 6, resp_acc_old.0[offset + 6]); // id
    if include_sk {
        missing_resps.insert(offset + 7, resp_acc_old.0[offset + 7]); // sk_enc
    }

    verify_partial_schnorr_resp_or_rmc!(
        rmc,
        resp_acc_new,
        new_gens,
        y_new,
        t_acc_new,
        challenge,
        missing_resps,
    );

    Ok(())
}

pub const AMOUNT_LABEL: &'static [u8; 6] = b"amount";

/// Public key of an account encrypted for auditors/mediators using twisted-Elgamal
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EncryptedPublicKey<G: AffineRepr> {
    /// Ephemeral key per auditor/mediator like `r * PK_i`
    pub eph_pk: Vec<G>,
    /// Encrypted account public key as `r * G + pk_{acct}`
    pub encrypted: G,
}

impl<G: AffineRepr> EncryptedPublicKey<G> {
    /// Decrypt to the get the public key of account using auditor/mediator secret key
    pub fn decrypt(&self, index: usize, mut sk: G::ScalarField) -> G {
        assert!(index < self.eph_pk.len());
        sk.inverse_in_place().unwrap();
        let mask = self.eph_pk[index] * sk;
        sk.zeroize();
        (self.encrypted - mask).into_affine()
    }
}

pub(crate) fn init_pk_enc_protocol<R: CryptoRngCore, G: AffineRepr, W: Write>(
    rng: &mut R,
    sk: G::ScalarField,
    sk_blinding: G::ScalarField,
    auditor_keys: Vec<G>,
    sk_gen: G,
    enc_key_gen: G,
    mut writer: W,
) -> Result<(
    Vec<PokDiscreteLogProtocol<G>>,
    PokPedersenCommitmentProtocol<G>,
    EncryptedPublicKey<G>,
)> {
    let mut r = G::ScalarField::rand(rng);
    let mut r_blinding = G::ScalarField::rand(rng);
    let eph_pk =
        G::Group::normalize_batch(&auditor_keys.iter().map(|pk| *pk * r).collect::<Vec<_>>());
    let encrypted = (enc_key_gen * r + sk_gen * sk).into_affine();

    let t_enc =
        PokPedersenCommitmentProtocol::init(r, r_blinding, &enc_key_gen, sk, sk_blinding, &sk_gen);
    let t_eph_pk = auditor_keys
        .iter()
        .map(|pk| PokDiscreteLogProtocol::init(r, r_blinding, pk))
        .collect::<Vec<_>>();

    let encrypted_pubkey = EncryptedPublicKey { eph_pk, encrypted };
    encrypted_pubkey.serialize_compressed(&mut writer)?;
    t_enc.challenge_contribution(
        &enc_key_gen,
        &sk_gen,
        &encrypted_pubkey.encrypted,
        &mut writer,
    )?;
    for (i, t) in t_eph_pk.iter().enumerate() {
        t.challenge_contribution(&auditor_keys[i], &encrypted_pubkey.eph_pk[i], &mut writer)?;
    }

    r.zeroize();
    r_blinding.zeroize();
    Ok((t_eph_pk, t_enc, encrypted_pubkey))
}

pub(crate) fn reps_pk_enc<G: AffineRepr>(
    t_eph_pk: Vec<PokDiscreteLogProtocol<G>>,
    t_enc: PokPedersenCommitmentProtocol<G>,
    challenge: &G::ScalarField,
) -> (
    Vec<PartialPokDiscreteLog<G>>,
    Partial1PokPedersenCommitment<G>,
) {
    let resp_enc = t_enc.gen_partial1_proof(challenge);
    let resp_eph_pk = t_eph_pk
        .into_iter()
        .map(|t| t.gen_partial_proof())
        .collect::<Vec<_>>();
    (resp_eph_pk, resp_enc)
}

pub(crate) fn chal_contrib_pk_enc<G: AffineRepr, W: Write>(
    resp_eph_pk: &[PartialPokDiscreteLog<G>],
    resp_enc: &Partial1PokPedersenCommitment<G>,
    encrypted_pubkey: &EncryptedPublicKey<G>,
    auditor_keys: &[G],
    sk_gen: G,
    enc_key_gen: G,
    mut writer: W,
) -> Result<()> {
    if encrypted_pubkey.eph_pk.len() != auditor_keys.len() {
        return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
            encrypted_pubkey.eph_pk.len(),
            auditor_keys.len(),
        ));
    }
    if resp_eph_pk.len() != auditor_keys.len() {
        return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
            resp_eph_pk.len(),
            auditor_keys.len(),
        ));
    }

    encrypted_pubkey.serialize_compressed(&mut writer)?;
    resp_enc.challenge_contribution(
        &enc_key_gen,
        &sk_gen,
        &encrypted_pubkey.encrypted,
        &mut writer,
    )?;
    for (i, r) in resp_eph_pk.iter().enumerate() {
        r.challenge_contribution(&auditor_keys[i], &encrypted_pubkey.eph_pk[i], &mut writer)?;
    }

    Ok(())
}

pub(crate) fn verify_pk_enc<G: AffineRepr>(
    resp_eph_pk: &[PartialPokDiscreteLog<G>],
    resp_enc: &Partial1PokPedersenCommitment<G>,
    encrypted_pubkey: &EncryptedPublicKey<G>,
    auditor_keys: &[G],
    challenge: &G::ScalarField,
    sk_response: &G::ScalarField,
    sk_gen: G,
    enc_key_gen: G,
    mut rmc: Option<&mut RandomizedMultChecker<G>>,
) -> Result<()> {
    verify_or_rmc_3!(
        rmc,
        resp_enc,
        "Account public key encryption verification failed",
        encrypted_pubkey.encrypted,
        enc_key_gen,
        sk_gen,
        challenge,
        sk_response,
    );
    for (i, r) in resp_eph_pk.iter().enumerate() {
        verify_or_rmc_2!(
            rmc,
            r,
            "Ephemeral public key encryption verification failed",
            encrypted_pubkey.eph_pk[i],
            auditor_keys[i],
            &challenge,
            &resp_enc.response1,
        );
    }
    Ok(())
}

fn acc_old_gens<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    b_blinding: Affine<G0>,
) -> [Affine<G0>; NUM_GENERATORS] {
    [
        account_comm_key.sk_gen(),
        account_comm_key.balance_gen(),
        account_comm_key.counter_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.current_rho_gen(),
        account_comm_key.randomness_gen(),
        account_comm_key.current_randomness_gen(),
        account_comm_key.id_gen(),
        account_comm_key.sk_enc_gen(),
        b_blinding,
    ]
}

fn acc_new_gens<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
) -> [Affine<G0>; NUM_GENERATORS - 1] {
    [
        account_comm_key.sk_gen(),
        account_comm_key.balance_gen(),
        account_comm_key.counter_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.current_rho_gen(),
        account_comm_key.randomness_gen(),
        account_comm_key.current_randomness_gen(),
        account_comm_key.id_gen(),
        account_comm_key.sk_enc_gen(),
    ]
}

fn acc_old_gens_host<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    b_blinding: Affine<G0>,
) -> [Affine<G0>; NUM_GENERATORS - 2] {
    [
        account_comm_key.balance_gen(),
        account_comm_key.counter_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.current_rho_gen(),
        account_comm_key.randomness_gen(),
        account_comm_key.current_randomness_gen(),
        account_comm_key.id_gen(),
        b_blinding,
    ]
}

fn acc_new_gens_host<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    b_blinding: Affine<G0>,
) -> [Affine<G0>; NUM_GENERATORS - 2] {
    [
        account_comm_key.balance_gen(),
        account_comm_key.counter_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.current_rho_gen(),
        account_comm_key.randomness_gen(),
        account_comm_key.current_randomness_gen(),
        account_comm_key.id_gen(),
        b_blinding,
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account::tests::{
        get_tree_with_account_comm, get_tree_with_commitment, setup_gens_new,
    };
    use crate::account_registration::tests::{new_account, new_account_without_sk};
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::util::{
        add_verification_tuples_batches_to_rmc, batch_verify_bp, handle_verification_tuples,
        prove_with_rng, verify_rmc, verify_with_rng,
    };
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use ark_ff::UniformRand;
    use ark_pallas::{Fr as PallasFr, PallasConfig};
    use ark_vesta::{Fr as VestaFr, VestaConfig};
    use curve_tree_relations::curve_tree::CurveTree;
    use rand::rngs::ThreadRng;
    use std::time::Instant;

    #[test]
    fn withdraw_proof() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let asset_id = 1;
        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .into_iter()
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = (0..num_auditor_keys)
            .map(|i| auditor_keys[i].1.0)
            .collect::<Vec<_>>();

        let (sk, account_pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, sk, sk_enc, id.clone());
        account.without_sk.balance = 100;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let withdraw_amount = 30;
        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_withdraw(withdraw_amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let (proof, nullifier) = WithdrawProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            withdraw_amount,
            &account,
            &updated_account,
            updated_account_comm,
            path,
            auditor_pubkeys.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify::<_, PallasParams, VestaParams>(
                asset_id,
                withdraw_amount,
                updated_account_comm,
                nullifier,
                auditor_pubkeys.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For withdraw txn");
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );

        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(proof.0.encrypted_pubkey.decrypt(i, sk.0), account_pk.0);
        }
    }

    #[test]
    fn deposit_proof() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let asset_id = 1;
        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .into_iter()
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = (0..num_auditor_keys)
            .map(|i| auditor_keys[i].1.0)
            .collect::<Vec<_>>();

        let (sk, account_pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account(&mut rng, asset_id, sk, sk_enc, id.clone());
        account.without_sk.balance = 50;

        let account_tree = get_tree_with_account_comm::<L, _>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let deposit_amount = 25;
        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_deposit(deposit_amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let (proof, nullifier) = DepositProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            deposit_amount,
            &account,
            &updated_account,
            updated_account_comm,
            path,
            auditor_pubkeys.clone(),
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
            enc_key_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify::<_, PallasParams, VestaParams>(
                asset_id,
                deposit_amount,
                updated_account_comm,
                nullifier,
                auditor_pubkeys.clone(),
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                &mut rng,
                None,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For deposit txn");
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );

        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(proof.0.encrypted_pubkey.decrypt(i, sk.0), account_pk.0);
        }
    }

    #[test]
    fn batch_withdraw_proofs() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let withdraw_amount = 30;
        let batch_size = 10;

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);

        let mut account_comms = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, sk, sk_enc, id);
            account.without_sk.balance = 100;
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &account_tree_params,
            Some(6),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_withdraw(withdraw_amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("batch_withdraw_nonce_{}", i).into_bytes())
            .collect();

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (proof, nullifier) = WithdrawProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                withdraw_amount,
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                auditor_pubkeys.clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
            )
            .unwrap();

            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let clock = Instant::now();

        for i in 0..batch_size {
            proofs[i]
                .verify::<_, PallasParams, VestaParams>(
                    asset_id,
                    withdraw_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
        }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples::<ThreadRng, PallasParams, VestaParams>(
                    asset_id,
                    withdraw_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        batch_verify_bp(
            even_tuples,
            odd_tuples,
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
        )
        .unwrap();

        let batch_verifier_time = clock.elapsed();

        println!(
            "For {batch_size} withdraw proofs, verifier time = {:?}, batch verifier time {:?}",
            verifier_time, batch_verifier_time
        );

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples::<ThreadRng, PallasParams, VestaParams>(
                    asset_id,
                    withdraw_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
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
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let batch_verifier_rmc_time = clock.elapsed();

        println!(
            "For {batch_size} withdraw proofs, batch verifier_rmc time {:?}",
            batch_verifier_rmc_time
        );
    }

    #[test]
    fn combined_withdraw_proofs() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 16;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let withdraw_amount = 30;
        let batch_size = 10;

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);

        let mut account_comms = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, sk, sk_enc, id);
            account.without_sk.balance = 100;
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &account_tree_params,
            Some(5),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_withdraw(withdraw_amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("combined_withdraw_nonce_{}", i).into_bytes())
            .collect();

        let clock = Instant::now();
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

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let (proof, nullifier) =
                WithdrawProof::new_with_given_prover::<_, PallasParams, VestaParams>(
                    &mut rng,
                    withdraw_amount,
                    &accounts[i],
                    &updated_accounts[i],
                    updated_account_comms[i],
                    paths[i].clone(),
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut even_prover,
                    &mut odd_prover,
                )
                .unwrap();
            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let (even_bp, odd_bp) = prove_with_rng(
            even_prover,
            odd_prover,
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rng,
        )
        .unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        for i in 0..batch_size {
            proofs[i]
                .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                    asset_id,
                    withdraw_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
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
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
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
                .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                    asset_id,
                    withdraw_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
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
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let rmc_verification_time = clock.elapsed();

        println!("Combined withdraw proving time = {:?}", proving_time);
        println!(
            "Combined withdraw verification time = {:?}",
            verification_time
        );
        println!(
            "Combined withdraw RMC verification time = {:?}",
            rmc_verification_time
        );
        println!(
            "Combined withdraw proof size = {} bytes",
            even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
        );
    }

    #[test]
    fn batch_deposit_proofs() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let deposit_amount = 25;
        let batch_size = 10;

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);

        let mut account_comms = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, sk, sk_enc, id);
            account.without_sk.balance = 50;
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &account_tree_params,
            Some(5),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_deposit(deposit_amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("batch_deposit_nonce_{}", i).into_bytes())
            .collect();

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (proof, nullifier) = DepositProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                deposit_amount,
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                auditor_pubkeys.clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
            )
            .unwrap();

            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let clock = Instant::now();

        for i in 0..batch_size {
            proofs[i]
                .verify::<_, PallasParams, VestaParams>(
                    asset_id,
                    deposit_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
        }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples::<ThreadRng, PallasParams, VestaParams>(
                    asset_id,
                    deposit_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut rng,
                    None,
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        batch_verify_bp(
            even_tuples,
            odd_tuples,
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
        )
        .unwrap();

        let batch_verifier_time = clock.elapsed();

        println!(
            "For {batch_size} deposit proofs, verifier time = {:?}, batch verifier time {:?}",
            verifier_time, batch_verifier_time
        );

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(PallasFr::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(VestaFr::rand(&mut rng));

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples::<ThreadRng, PallasParams, VestaParams>(
                    asset_id,
                    deposit_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
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
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let batch_verifier_rmc_time = clock.elapsed();

        println!(
            "For {batch_size} deposit proofs, batch verifier_rmc time {:?}",
            batch_verifier_rmc_time
        );
    }

    #[test]
    fn combined_deposit_proofs() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 16;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let deposit_amount = 25;
        let batch_size = 10;

        let enc_key_gen = account_comm_key.sk_enc_gen();

        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let mut accounts = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);

        let mut account_comms = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let (sk_enc, _) = keygen_enc(&mut rng, enc_key_gen);
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _, _) = new_account(&mut rng, asset_id, sk, sk_enc, id);
            account.without_sk.balance = 50;
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            accounts.push(account);
            account_comms.push(account_comm);
        }

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasConfig, VestaConfig>::from_leaves(
            &set,
            &account_tree_params,
            Some(5),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_deposit(deposit_amount).unwrap();
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();

            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("combined_deposit_nonce_{}", i).into_bytes())
            .collect();

        let clock = Instant::now();
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

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let (proof, nullifier) =
                DepositProof::new_with_given_prover::<_, PallasParams, VestaParams>(
                    &mut rng,
                    deposit_amount,
                    &accounts[i],
                    &updated_accounts[i],
                    updated_account_comms[i],
                    paths[i].clone(),
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut even_prover,
                    &mut odd_prover,
                )
                .unwrap();
            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let (even_bp, odd_bp) = prove_with_rng(
            even_prover,
            odd_prover,
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rng,
        )
        .unwrap();
        let proving_time = clock.elapsed();

        let clock = Instant::now();
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        for i in 0..batch_size {
            proofs[i]
                .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                    asset_id,
                    deposit_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
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
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
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
                .verify_sigma_protocols_and_enforce_constraints::<PallasParams, VestaParams>(
                    asset_id,
                    deposit_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    auditor_pubkeys.clone(),
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
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
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let rmc_verification_time = clock.elapsed();

        println!("Combined deposit proving time = {:?}", proving_time);
        println!(
            "Combined deposit verification time = {:?}",
            verification_time
        );
        println!(
            "Combined deposit RMC verification time = {:?}",
            rmc_verification_time
        );
        println!(
            "Combined deposit proof size = {} bytes",
            even_bp.compressed_size() + odd_bp.compressed_size() + proofs.compressed_size()
        );
    }

    #[test]
    fn withdraw_proof_parallel() {
        // W2 (Parallel): Host creates partial + host account commitment proof.
        // Ledger independently creates AuthProofTransparent.
        // Verifier checks both independently.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let asset_id = 1;
        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let (sk, account_pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account_without_sk(&mut rng, asset_id, id);
        account.balance = 100;

        let account_comm = AccountStateCommitment::from_without_sk(
            account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let account_tree =
            get_tree_with_commitment::<L, _>(account_comm.clone(), &account_tree_params, 6);

        let withdraw_amount = 30;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_withdraw(withdraw_amount).unwrap();
        let updated_account_comm = AccountStateCommitment::from_without_sk(
            updated_account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host side: creates partial + host account commitment (without sk)
        let (partial, host_proof, rerandomized_leaf, rand_part_old_comm, rand_new_comm, nullifier) =
            WithdrawSplitProtocol::<L, PallasFr, VestaFr, PallasConfig, VestaConfig>::new::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                withdraw_amount,
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

        //  Ledger side: creates AuthProofTransparent on its own AUTH_TXN_LABEL transcript
        let sk_gen = account_comm_key.sk_gen();
        let pc_gens = account_tree_params.even_parameters.pc_gens();

        let b_blinding = pc_gens.B_blinding;

        let auth_proof = AuthProofTransparent::new(
            &mut rng,
            sk.0,
            sk_enc.0,
            rand_part_old_comm,
            rand_new_comm,
            &rerandomized_leaf,
            &updated_account_comm.0,
            nullifier,
            auditor_pubkeys.clone(),
            nonce,
            sk_gen,
            enc_key_gen,
            b_blinding,
        )
        .unwrap();

        let proof = WithdrawSplitProof(CommonTransparentSplitProof {
            partial,
            commitment_proof: TransparentCommitmentsSplitProof {
                auth_proof,
                host_proof,
            },
        });

        //  verify host portion and auth portion independently

        // 1. Verify host
        let (even_tuple, odd_tuple, _) = proof
            .0
            .verify_host_and_return_tuples::<_, PallasParams, VestaParams>(
                asset_id,
                withdraw_amount,
                updated_account_comm,
                nullifier,
                true,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();

        // 2. Verify auth proof independently (its own AUTH_TXN_LABEL transcript)
        proof
            .0
            .commitment_proof
            .auth_proof
            .verify(
                &rerandomized_leaf,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                nonce,
                sk_gen,
                enc_key_gen,
                b_blinding,
                None,
            )
            .unwrap();

        // Verify decryption works
        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(
                proof
                    .0
                    .commitment_proof
                    .auth_proof
                    .encrypted_pubkeys
                    .decrypt(i, sk.0),
                account_pk.0
            );
        }
    }

    #[test]
    fn withdraw_proof_sequential() {
        // W3 (Sequential): Host creates partial + host account commitment, derives challenge_h.
        // Host sends challenge_h to Ledger. Ledger uses ledger_nonce = challenge_h_bytes || original_nonce.
        // Verifier derives challenge_h, verifies host, reconstructs ledger_nonce, verifies auth.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let asset_id = 1;
        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let (sk, account_pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account_without_sk(&mut rng, asset_id, id);
        account.balance = 100;

        let account_comm = AccountStateCommitment::from_without_sk(
            account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let account_tree =
            get_tree_with_commitment::<L, _>(account_comm.clone(), &account_tree_params, 6);

        let withdraw_amount = 30;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_withdraw(withdraw_amount).unwrap();
        let updated_account_comm = AccountStateCommitment::from_without_sk(
            updated_account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host creates partial + host account commitment
        let (protocol, mut even_prover, odd_prover, nullifier) =
            WithdrawSplitProtocol::<L, PallasFr, VestaFr, PallasConfig, VestaConfig>::init::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                withdraw_amount,
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

        //  Derive challenge_h externally and send to Ledger
        let challenge_h = {
            let transcript = even_prover.transcript();
            transcript.challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
        };
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        let rerandomized_leaf = protocol.rerandomized_leaf();

        let sk_gen = account_comm_key.sk_gen();
        let pc_gens = account_tree_params.even_parameters.pc_gens();
        let b_blinding = pc_gens.B_blinding;

        let auth_proof = AuthProofTransparent::new(
            &mut rng,
            sk.0,
            sk_enc.0,
            protocol.rand_part_old_comm(),
            protocol.rand_new_comm(),
            &rerandomized_leaf,
            &updated_account_comm.0,
            nullifier,
            auditor_pubkeys.clone(),
            &ledger_nonce,
            sk_gen,
            enc_key_gen,
            b_blinding,
        )
        .unwrap();

        // Host hashes auth_proof into the transcript to derive an updated challenge
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

        //  Generate host proof and assemble split proof
        let (partial, host_proof) = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_final,
                even_prover,
                odd_prover,
                &account_tree_params,
                &mut rng,
            )
            .unwrap();
        let proof = WithdrawSplitProof(CommonTransparentSplitProof {
            partial,
            commitment_proof: TransparentCommitmentsSplitProof {
                auth_proof,
                host_proof,
            },
        });

        //  derive challenge_h from host, reconstruct ledger_nonce, verify both

        // 1. Derive challenge_h from verifier's transcript
        let (mut even_verifier, odd_verifier, challenge_h_v) = proof
            .0
            .challenge_contribution::<PallasParams, VestaParams>(
                asset_id,
                withdraw_amount,
                updated_account_comm,
                nullifier,
                true,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        // 2. Reconstruct ledger_nonce from verifier's challenge_h
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        // 3. Verify auth proof with reconstructed ledger_nonce
        proof
            .0
            .commitment_proof
            .auth_proof
            .verify(
                &rerandomized_leaf,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                &ledger_nonce_v,
                sk_gen,
                enc_key_gen,
                b_blinding,
                None,
            )
            .unwrap();

        // Verifier hashes auth_proof into the transcript to derive the updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        proof
            .0
            .commitment_proof
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        even_verifier
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = even_verifier
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

        let (even_tuple, odd_tuple) = proof
            .0
            .verify_host_and_return_tuples_with_challenge::<_, PallasParams, VestaParams>(
                &challenge_h_final_v,
                even_verifier,
                odd_verifier,
                asset_id,
                withdraw_amount,
                updated_account_comm,
                nullifier,
                true,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();

        // Verify decryption works
        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(
                proof
                    .0
                    .commitment_proof
                    .auth_proof
                    .encrypted_pubkeys
                    .decrypt(i, sk.0),
                account_pk.0
            );
        }
    }

    #[test]
    fn deposit_proof_parallel() {
        // W2 (Parallel): Host creates partial + host account commitment proof for deposit.
        // Ledger independently creates AuthProofTransparent.
        // Verifier checks both independently.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let asset_id = 1;
        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let (sk, account_pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account_without_sk(&mut rng, asset_id, id);
        account.balance = 50;

        let account_comm = AccountStateCommitment::from_without_sk(
            account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let account_tree =
            get_tree_with_commitment::<L, _>(account_comm.clone(), &account_tree_params, 6);

        let deposit_amount = 25;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_deposit(deposit_amount).unwrap();
        let updated_account_comm = AccountStateCommitment::from_without_sk(
            updated_account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host side: creates partial + host account commitment (without sk)
        let (partial, host_proof, rerandomized_leaf, rand_part_old_comm, rand_new_comm, nullifier) =
            DepositSplitProtocol::<L, PallasFr, VestaFr, PallasConfig, VestaConfig>::new::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                deposit_amount,
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

        //  Ledger side: creates AuthProofTransparent on its own AUTH_TXN_LABEL transcript
        let sk_gen = account_comm_key.sk_gen();
        let pc_gens = account_tree_params.even_parameters.pc_gens();
        let b_blinding = pc_gens.B_blinding;

        let auth_proof = AuthProofTransparent::new(
            &mut rng,
            sk.0,
            sk_enc.0,
            rand_part_old_comm,
            rand_new_comm,
            &rerandomized_leaf,
            &updated_account_comm.0,
            nullifier,
            auditor_pubkeys.clone(),
            nonce,
            sk_gen,
            enc_key_gen,
            b_blinding,
        )
        .unwrap();

        let proof = DepositSplitProof(CommonTransparentSplitProof {
            partial,
            commitment_proof: TransparentCommitmentsSplitProof {
                auth_proof,
                host_proof,
            },
        });

        //  verify host portion and auth portion independently

        // 1. Verify host
        let (even_tuple, odd_tuple, _challenge_h_v) = proof
            .0
            .verify_host_and_return_tuples::<_, PallasParams, VestaParams>(
                asset_id,
                deposit_amount,
                updated_account_comm,
                nullifier,
                false,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();

        // 2. Verify auth proof independently (its own AUTH_TXN_LABEL transcript)
        proof
            .0
            .commitment_proof
            .auth_proof
            .verify(
                &rerandomized_leaf,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                nonce,
                sk_gen,
                enc_key_gen,
                b_blinding,
                None,
            )
            .unwrap();

        // Verify decryption works
        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(
                proof
                    .0
                    .commitment_proof
                    .auth_proof
                    .encrypted_pubkeys
                    .decrypt(i, sk.0),
                account_pk.0
            );
        }
    }

    #[test]
    fn deposit_proof_sequential() {
        // W3 (Sequential): Host creates partial + host account commitment for deposit, derives challenge_h.
        // Host sends challenge_h to Ledger. Ledger uses ledger_nonce = challenge_h_bytes || original_nonce.
        // Verifier derives challenge_h, verifies host, reconstructs ledger_nonce, verifies auth.

        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let enc_key_gen = account_comm_key.sk_enc_gen();
        let asset_id = 1;
        let num_auditor_keys = 2;
        let auditor_keys = (0..num_auditor_keys)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let auditor_pubkeys = auditor_keys.iter().map(|k| k.1.0).collect::<Vec<_>>();

        let (sk, account_pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (sk_enc, pk_enc) = keygen_enc(&mut rng, enc_key_gen);
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _, _) = new_account_without_sk(&mut rng, asset_id, id);
        account.balance = 50;

        let account_comm = AccountStateCommitment::from_without_sk(
            account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let account_tree =
            get_tree_with_commitment::<L, _>(account_comm.clone(), &account_tree_params, 6);

        let deposit_amount = 25;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_deposit(deposit_amount).unwrap();
        let updated_account_comm = AccountStateCommitment::from_without_sk(
            updated_account.commit(account_comm_key.clone()).unwrap(),
            account_pk.0,
            pk_enc.0,
        );

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host creates partial + host account commitment
        let (protocol, mut even_prover, odd_prover, nullifier) =
            DepositSplitProtocol::<L, PallasFr, VestaFr, PallasConfig, VestaConfig>::init::<
                _,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                deposit_amount,
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

        //  Derive challenge_h externally and send to Ledger
        let challenge_h = {
            let transcript = even_prover.transcript();
            transcript.challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL)
        };
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        let rerandomized_leaf = protocol.rerandomized_leaf();

        let sk_gen = account_comm_key.sk_gen();
        let pc_gens = account_tree_params.even_parameters.pc_gens();
        let b_blinding = pc_gens.B_blinding;

        let auth_proof = AuthProofTransparent::new(
            &mut rng,
            sk.0,
            sk_enc.0,
            protocol.rand_part_old_comm(),
            protocol.rand_new_comm(),
            &rerandomized_leaf,
            &updated_account_comm.0,
            nullifier,
            auditor_pubkeys.clone(),
            &ledger_nonce,
            sk_gen,
            enc_key_gen,
            b_blinding,
        )
        .unwrap();

        // Host hashes auth_proof into the transcript to derive an updated challenge
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

        //  Generate host proof and assemble split proof
        let (partial, host_proof) = protocol
            .gen_proof::<_, PallasParams, VestaParams>(
                &challenge_h_final,
                even_prover,
                odd_prover,
                &account_tree_params,
                &mut rng,
            )
            .unwrap();
        let proof = DepositSplitProof(CommonTransparentSplitProof {
            partial,
            commitment_proof: TransparentCommitmentsSplitProof {
                auth_proof,
                host_proof,
            },
        });

        //  derive challenge_h from host, reconstruct ledger_nonce, verify both

        // 1. Derive challenge_h from verifier's transcript
        let (mut even_verifier, odd_verifier, challenge_h_v) = proof
            .0
            .challenge_contribution::<PallasParams, VestaParams>(
                asset_id,
                deposit_amount,
                updated_account_comm,
                nullifier,
                false,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        // 2. Reconstruct ledger_nonce from verifier's challenge_h
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        // 3. Verify auth proof with reconstructed ledger_nonce
        proof
            .0
            .commitment_proof
            .auth_proof
            .verify(
                &rerandomized_leaf,
                &updated_account_comm.0,
                nullifier,
                &auditor_pubkeys,
                &ledger_nonce_v,
                sk_gen,
                enc_key_gen,
                b_blinding,
                None,
            )
            .unwrap();

        // Verifier hashes auth_proof into the transcript to derive the updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        proof
            .0
            .commitment_proof
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        even_verifier
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = even_verifier
            .transcript()
            .challenge_scalar::<PallasFr>(TXN_CHALLENGE_LABEL);

        let (even_tuple, odd_tuple) = proof
            .0
            .verify_host_and_return_tuples_with_challenge::<_, PallasParams, VestaParams>(
                &challenge_h_final_v,
                even_verifier,
                odd_verifier,
                asset_id,
                deposit_amount,
                updated_account_comm,
                nullifier,
                false,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();

        // Verify decryption works
        for (i, (sk, _)) in auditor_keys.into_iter().enumerate() {
            assert_eq!(
                proof
                    .0
                    .commitment_proof
                    .auth_proof
                    .encrypted_pubkeys
                    .decrypt(i, sk.0),
                account_pk.0
            );
        }
    }
}
