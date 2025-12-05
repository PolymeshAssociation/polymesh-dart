use crate::account::common::{ensure_correct_balance_change, ensure_same_accounts};
use crate::account::state::NUM_GENERATORS;
use crate::account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment};
use crate::util::{
    add_verification_tuples_to_rmc, bp_gens_for_vec_commitment,
    enforce_constraints_for_randomness_relations, get_verification_tuples_with_rng, prove_with_rng,
    verify_given_verification_tuples,
};
use crate::{
    ASSET_ID_LABEL, Error, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_CHALLENGE_LABEL,
    TXN_EVEN_LABEL, TXN_ODD_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript,
    error::Result,
};
use ark_ec::CurveGroup;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSProof, VerificationTuple, Verifier};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
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

pub const AMOUNT_LABEL: &'static [u8; 6] = b"amount";

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BPProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
}

fn ensure_counter_unchanged<G>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
) -> Result<()>
where
    G: ark_ec::AffineRepr,
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

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
struct CommonTransparentProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    r1cs_proof: Option<BPProof<F0, F1, G0, G1>>,
    re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    t_r_leaf: Affine<G0>,
    t_acc_new: Affine<G0>,
    resp_leaf: SchnorrResponse<Affine<G0>>,
    resp_acc_new: PartialSchnorrResponse<Affine<G0>>,
    resp_null: PartialPokDiscreteLog<Affine<G0>>,
    comm_bp: Affine<G0>,
    t_bp: Affine<G0>,
    resp_bp: PartialSchnorrResponse<Affine<G0>>,
    resp_eph_pk: Vec<PartialPokDiscreteLog<Affine<G0>>>,
    resp_enc: Partial1PokPedersenCommitment<Affine<G0>>,
    pub encrypted_pubkeys: EncryptedPublicKey<G0>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonTransparentProof<L, F0, F1, G0, G1>
{
    fn new<R: CryptoRngCore>(
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
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
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

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params, rng)?;

        proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((proof, nullifier))
    }

    fn new_with_given_prover<'a, R: CryptoRngCore>(
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
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_same_accounts(account, updated_account, true)?;
        ensure_correct_balance_change(account, updated_account, amount, has_balance_decreased)?;
        ensure_counter_unchanged(account, updated_account)?;

        let (re_randomized_path, mut rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
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
            AMOUNT_LABEL,
            amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let mut sk_blinding = F0::rand(rng);
        let mut new_balance_blinding = F0::rand(rng);
        let mut counter_blinding = F0::rand(rng);
        let mut initial_rho_blinding = F0::rand(rng);
        let mut old_rho_blinding = F0::rand(rng);
        let mut new_rho_blinding = F0::rand(rng);
        let mut old_s_blinding = F0::rand(rng);
        let mut new_s_blinding = F0::rand(rng);
        let mut id_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.current_rho_gen();
        let nullifier = account.nullifier(&account_comm_key);

        let t_r_leaf = SchnorrCommitment::new(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
            vec![
                sk_blinding,
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                old_rho_blinding,
                old_s_blinding,
                id_blinding,
                F0::rand(rng),
            ],
        );

        let t_acc_new = SchnorrCommitment::new(
            &Self::acc_new_gens(account_comm_key.clone()),
            vec![
                sk_blinding,
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                new_rho_blinding,
                new_s_blinding,
                id_blinding,
            ],
        );

        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, old_rho_blinding, &nullifier_gen);

        let sk_gen = account_comm_key.sk_gen();
        let mut r = F0::rand(rng);
        let mut r_blinding = F0::rand(rng);
        let eph_pk =
            Projective::normalize_batch(&auditor_keys.iter().map(|pk| *pk * r).collect::<Vec<_>>());
        let encrypted = (enc_key_gen * r + sk_gen * account.sk).into_affine();

        let t_enc = PokPedersenCommitmentProtocol::init(
            r,
            r_blinding,
            &enc_key_gen,
            account.sk,
            sk_blinding,
            &sk_gen,
        );
        let t_eph_pk = auditor_keys
            .iter()
            .map(|pk| PokDiscreteLogProtocol::init(r, r_blinding, pk))
            .collect::<Vec<_>>();

        t_r_leaf.challenge_contribution(&mut transcript)?;
        t_acc_new.challenge_contribution(&mut transcript)?;
        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        let encrypted_pubkeys = EncryptedPublicKey { eph_pk, encrypted };
        encrypted_pubkeys.serialize_compressed(&mut transcript)?;
        t_enc.challenge_contribution(
            &enc_key_gen,
            &sk_gen,
            &encrypted_pubkeys.encrypted,
            &mut transcript,
        )?;
        for (i, t) in t_eph_pk.iter().enumerate() {
            t.challenge_contribution(
                &auditor_keys[i],
                &encrypted_pubkeys.eph_pk[i],
                &mut transcript,
            )?;
        }

        let _ = transcript;

        let mut comm_bp_blinding = F0::rand(rng);
        let (comm_bp, vars) = if has_balance_decreased {
            let (comm_bp, mut vars) = even_prover.commit_vec(
                &[
                    account.rho,
                    account.current_rho,
                    updated_account.current_rho,
                    account.randomness,
                    updated_account.randomness,
                    updated_account.balance.into(),
                ],
                comm_bp_blinding,
                &account_tree_params.even_parameters.bp_gens,
            );
            // Enforce range proof only during withdraw
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
                    updated_account.randomness,
                ],
                comm_bp_blinding,
                &account_tree_params.even_parameters.bp_gens,
            )
        };
        enforce_constraints_for_randomness_relations(even_prover, vars);

        let mut transcript = even_prover.transcript();

        let t_bp = if has_balance_decreased {
            SchnorrCommitment::new(
                &Self::bp_gens_vec_bal_decr(account_tree_params),
                vec![
                    F0::rand(rng),
                    initial_rho_blinding,
                    old_rho_blinding,
                    new_rho_blinding,
                    old_s_blinding,
                    new_s_blinding,
                    new_balance_blinding,
                ],
            )
        } else {
            SchnorrCommitment::new(
                &Self::bp_gens_vec(account_tree_params),
                vec![
                    F0::rand(rng),
                    initial_rho_blinding,
                    old_rho_blinding,
                    new_rho_blinding,
                    old_s_blinding,
                    new_s_blinding,
                ],
            )
        };

        t_bp.challenge_contribution(&mut transcript)?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let mut wits = [
            account.sk,
            updated_account.balance.into(),
            account.counter.into(),
            account.rho,
            account.current_rho,
            account.randomness,
            account.id,
            rerandomization,
        ];
        let resp_leaf = t_r_leaf.response(&wits, &challenge)?;
        Zeroize::zeroize(&mut wits);

        let mut wits = BTreeMap::new();
        wits.insert(4, updated_account.current_rho);
        wits.insert(5, updated_account.randomness);
        let resp_acc_new = t_acc_new.partial_response(wits, &challenge)?;

        let resp_null = t_null.gen_partial_proof();

        let resp_enc = t_enc.gen_partial1_proof(&challenge);
        let resp_eph_pk = t_eph_pk
            .into_iter()
            .map(|t| t.gen_partial_proof())
            .collect::<Vec<_>>();

        let mut w = BTreeMap::new();
        w.insert(0, comm_bp_blinding);
        let resp_bp = t_bp.partial_response(w, &challenge)?;

        sk_blinding.zeroize();
        new_balance_blinding.zeroize();
        counter_blinding.zeroize();
        initial_rho_blinding.zeroize();
        old_rho_blinding.zeroize();
        new_rho_blinding.zeroize();
        old_s_blinding.zeroize();
        new_s_blinding.zeroize();
        id_blinding.zeroize();
        comm_bp_blinding.zeroize();
        rerandomization.zeroize();
        r.zeroize();
        r_blinding.zeroize();

        Ok((
            Self {
                r1cs_proof: None,
                re_randomized_path,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
                resp_leaf,
                resp_acc_new,
                resp_null,
                comm_bp,
                t_bp: t_bp.t,
                resp_bp,
                resp_enc,
                resp_eph_pk,
                encrypted_pubkeys,
            },
            nullifier,
        ))
    }

    fn verify<R: CryptoRngCore>(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
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

        let (even_tuple, odd_tuple) = self.verify_and_return_tuples(
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

    fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

        self.verify_sigma_protocols_and_enforce_constraints(
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

    fn verify_sigma_protocols_and_enforce_constraints(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        has_balance_decreased: bool,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        if self.resp_leaf.len() != NUM_GENERATORS {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                NUM_GENERATORS,
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
                1,
                self.resp_bp.responses.len(),
            ));
        }
        if self.encrypted_pubkeys.eph_pk.len() != auditor_keys.len() {
            return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
                self.encrypted_pubkeys.eph_pk.len(),
                auditor_keys.len(),
            ));
        }
        if self.resp_eph_pk.len() != auditor_keys.len() {
            return Err(Error::EncryptionOrProofsNotPresentForAllKeys(
                self.resp_eph_pk.len(),
                auditor_keys.len(),
            ));
        }

        let _ = self
            .re_randomized_path
            .select_and_rerandomize_verifier_gadget(
                root,
                even_verifier,
                odd_verifier,
                &account_tree_params,
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
            AMOUNT_LABEL,
            amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.current_rho_gen();

        self.t_r_leaf.serialize_compressed(&mut transcript)?;
        self.t_acc_new.serialize_compressed(&mut transcript)?;
        self.resp_null
            .challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        let sk_gen = account_comm_key.sk_gen();

        self.encrypted_pubkeys
            .serialize_compressed(&mut transcript)?;
        self.resp_enc.challenge_contribution(
            &enc_key_gen,
            &sk_gen,
            &self.encrypted_pubkeys.encrypted,
            &mut transcript,
        )?;
        for (i, r) in self.resp_eph_pk.iter().enumerate() {
            r.challenge_contribution(
                &auditor_keys[i],
                &self.encrypted_pubkeys.eph_pk[i],
                &mut transcript,
            )?;
        }

        let _ = transcript;

        let vars = if has_balance_decreased {
            let mut vars = even_verifier.commit_vec(6, self.comm_bp);
            let new_bal_var = vars.pop().unwrap();
            range_proof(even_verifier, new_bal_var.into(), None, BALANCE_BITS.into())?;
            vars
        } else {
            even_verifier.commit_vec(5, self.comm_bp)
        };

        enforce_constraints_for_randomness_relations(even_verifier, vars);

        let mut transcript = even_verifier.transcript();

        self.t_bp.serialize_compressed(&mut transcript)?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let mut y = self.re_randomized_path.get_rerandomized_leaf() - asset_id_comm;
        if has_balance_decreased {
            y = y - (account_comm_key.balance_gen() * F0::from(amount));
        } else {
            y = y + (account_comm_key.balance_gen() * F0::from(amount));
        }

        let y_new = updated_account_commitment.0 - asset_id_comm;

        let mut missing_resps_acc_new = BTreeMap::new();
        missing_resps_acc_new.insert(0, self.resp_leaf.0[0]);
        missing_resps_acc_new.insert(1, self.resp_leaf.0[1]);
        missing_resps_acc_new.insert(2, self.resp_leaf.0[2]);
        missing_resps_acc_new.insert(3, self.resp_leaf.0[3]);
        missing_resps_acc_new.insert(6, self.resp_leaf.0[6]);

        let mut missing_resps_bp = BTreeMap::new();
        missing_resps_bp.insert(1, self.resp_leaf.0[3]);
        missing_resps_bp.insert(2, self.resp_leaf.0[4]);
        missing_resps_bp.insert(3, self.resp_acc_new.responses[&4]);
        missing_resps_bp.insert(4, self.resp_leaf.0[5]);
        missing_resps_bp.insert(5, self.resp_acc_new.responses[&5]);
        if has_balance_decreased {
            missing_resps_bp.insert(6, self.resp_leaf.0[1]);
        }

        match rmc.as_mut() {
            Some(rmc) => {
                self.resp_leaf.verify_using_randomized_mult_checker(
                    Self::leaf_gens(account_comm_key.clone(), account_tree_params).to_vec(),
                    y.into_affine(),
                    self.t_r_leaf,
                    &challenge,
                    rmc,
                )?;
                self.resp_acc_new.verify_using_randomized_mult_checker(
                    Self::acc_new_gens(account_comm_key.clone()).to_vec(),
                    y_new.into_affine(),
                    self.t_acc_new,
                    &challenge,
                    missing_resps_acc_new,
                    rmc,
                )?;
                self.resp_null.verify_using_randomized_mult_checker(
                    nullifier,
                    nullifier_gen,
                    &challenge,
                    &self.resp_leaf.0[4],
                    rmc,
                );
                self.resp_enc.verify_using_randomized_mult_checker(
                    self.encrypted_pubkeys.encrypted,
                    enc_key_gen,
                    sk_gen,
                    &challenge,
                    &self.resp_leaf.0[0],
                    rmc,
                );
                for (i, r) in self.resp_eph_pk.iter().enumerate() {
                    r.verify_using_randomized_mult_checker(
                        self.encrypted_pubkeys.eph_pk[i],
                        auditor_keys[i],
                        &challenge,
                        &self.resp_enc.response1,
                        rmc,
                    );
                }
                if has_balance_decreased {
                    self.resp_bp.verify_using_randomized_mult_checker(
                        Self::bp_gens_vec_bal_decr(account_tree_params).to_vec(),
                        self.comm_bp,
                        self.t_bp,
                        &challenge,
                        missing_resps_bp,
                        rmc,
                    )?;
                } else {
                    self.resp_bp.verify_using_randomized_mult_checker(
                        Self::bp_gens_vec(account_tree_params).to_vec(),
                        self.comm_bp,
                        self.t_bp,
                        &challenge,
                        missing_resps_bp,
                        rmc,
                    )?;
                }
            }
            None => {
                self.resp_leaf.is_valid(
                    &Self::leaf_gens(account_comm_key.clone(), account_tree_params),
                    &y.into_affine(),
                    &self.t_r_leaf,
                    &challenge,
                )?;
                self.resp_acc_new.is_valid(
                    &Self::acc_new_gens(account_comm_key.clone()),
                    &y_new.into_affine(),
                    &self.t_acc_new,
                    &challenge,
                    missing_resps_acc_new,
                )?;
                if !self.resp_null.verify(
                    &nullifier,
                    &nullifier_gen,
                    &challenge,
                    &self.resp_leaf.0[4],
                ) {
                    return Err(Error::ProofVerificationError(
                        "Nullifier proof verification failed".to_string(),
                    ));
                }
                if !self.resp_enc.verify(
                    &self.encrypted_pubkeys.encrypted,
                    &enc_key_gen,
                    &sk_gen,
                    &challenge,
                    &self.resp_leaf.0[0],
                ) {
                    return Err(Error::ProofVerificationError(
                        "Account public key encryption verification failed".to_string(),
                    ));
                }
                for (i, r) in self.resp_eph_pk.iter().enumerate() {
                    if !r.verify(
                        &self.encrypted_pubkeys.eph_pk[i],
                        &auditor_keys[i],
                        &challenge,
                        &self.resp_enc.response1,
                    ) {
                        return Err(Error::ProofVerificationError(
                            "Ephemeral public key encryption verification failed".to_string(),
                        ));
                    }
                }
                if has_balance_decreased {
                    self.resp_bp.is_valid(
                        &Self::bp_gens_vec_bal_decr(account_tree_params),
                        &self.comm_bp,
                        &self.t_bp,
                        &challenge,
                        missing_resps_bp,
                    )?;
                } else {
                    self.resp_bp.is_valid(
                        &Self::bp_gens_vec(account_tree_params),
                        &self.comm_bp,
                        &self.t_bp,
                        &challenge,
                        missing_resps_bp,
                    )?;
                }
            }
        }

        Ok(())
    }

    fn leaf_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        account_tree_params: &SelRerandParameters<G0, G1>,
    ) -> [Affine<G0>; NUM_GENERATORS] {
        [
            account_comm_key.sk_gen(),
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
    ) -> [Affine<G0>; NUM_GENERATORS - 1] {
        [
            account_comm_key.sk_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            account_comm_key.id_gen(),
        ]
    }

    fn bp_gens_vec_bal_decr(account_tree_params: &SelRerandParameters<G0, G1>) -> [Affine<G0>; 7] {
        let mut gens = bp_gens_for_vec_commitment(6, &account_tree_params.even_parameters.bp_gens);
        [
            account_tree_params.even_parameters.pc_gens.B_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
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

/// Public key of an account encrypted for auditors/mediators using twisted-Elgamal
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct EncryptedPublicKey<G: SWCurveConfig + Copy + Clone> {
    /// Ephemeral key per auditor/mediator like `r * PK_i`
    pub eph_pk: Vec<Affine<G>>,
    /// Encrypted account public key as `r * G + pk_{acct}`
    pub encrypted: Affine<G>,
}

impl<G: SWCurveConfig + Copy + Clone> EncryptedPublicKey<G> {
    /// Decrypt to the get the public key of account using auditor/mediator secret key
    pub fn decrypt(&self, index: usize, mut sk: G::ScalarField) -> Affine<G> {
        assert!(index < self.eph_pk.len());
        sk.inverse_in_place().unwrap();
        let mask = self.eph_pk[index] * sk;
        sk.zeroize();
        (self.encrypted - mask).into_affine()
    }
}

/// Proof that a public amount was withdrawn from the account. Reveals the asset-id and amount but nothing else.
/// Commonly called "unshielding"
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
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> WithdrawProof<L, F0, F1, G0, G1>
{
    /// `auditor_keys` is the list auditor/mediator keys for which encryption of account public key is done
    /// `nonce` should include all the relevant information including the "transparent public key"
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) = CommonTransparentProof::new(
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) = CommonTransparentProof::new_with_given_prover(
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
    pub fn verify<R: CryptoRngCore>(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        self.0.verify(
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

    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        self.0.verify_and_return_tuples(
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

    pub fn verify_sigma_protocols_and_enforce_constraints(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        self.0.verify_sigma_protocols_and_enforce_constraints(
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

/// Proof that a public amount was deposited to the account. Reveals the asset-id and amount but nothing else.
/// Commonly called "shielding"
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
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> DepositProof<L, F0, F1, G0, G1>
{
    /// `auditor_keys` is the list auditor/mediator keys for which encryption of account public key is done
    /// `nonce` should include all the relevant information including the "transparent public key"
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) = CommonTransparentProof::new(
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

    pub fn new_with_given_prover<'a, R: CryptoRngCore>(
        rng: &mut R,
        amount: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (common, nullifier) = CommonTransparentProof::new_with_given_prover(
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
    pub fn verify<R: CryptoRngCore>(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        self.0.verify(
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

    pub fn verify_and_return_tuples<R: CryptoRngCore>(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        self.0.verify_and_return_tuples(
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

    pub fn verify_sigma_protocols_and_enforce_constraints(
        &self,
        asset_id: AssetId,
        amount: Balance,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        auditor_keys: Vec<Affine<G0>>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        self.0.verify_sigma_protocols_and_enforce_constraints(
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account::tests::{get_tree_with_account_comm, setup_gens};
    use crate::account_registration::tests::new_account;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::util::{
        add_verification_tuples_batches_to_rmc, batch_verify_bp, prove_with_rng, verify_rmc,
        verify_with_rng,
    };
    use ark_ff::UniformRand;
    use curve_tree_relations::curve_tree::CurveTree;
    use std::time::Instant;

    type PallasA = ark_pallas::Affine;
    type PallasFr = ark_pallas::Fr;
    type VestaFr = ark_vesta::Fr;
    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;

    #[test]
    fn withdraw_proof() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, _) =
            setup_gens::<NUM_GENS>(b"testing");

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
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id.clone());
        account.balance = 100;

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let withdraw_amount = 30;
        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_withdraw(withdraw_amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let (proof, nullifier) = WithdrawProof::new(
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
            .verify(
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
            assert_eq!(proof.0.encrypted_pubkeys.decrypt(i, sk.0), account_pk.0);
        }

        assert!(
            proof
                .verify(
                    asset_id,
                    withdraw_amount + 10,
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
                .is_err()
        );

        assert!(
            proof
                .verify(
                    asset_id,
                    withdraw_amount,
                    updated_account_comm,
                    PallasA::rand(&mut rng),
                    auditor_pubkeys.clone(),
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut rng,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    asset_id + 1,
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
                .is_err()
        );
    }

    #[test]
    fn deposit_proof() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 12;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, _) =
            setup_gens::<NUM_GENS>(b"testing");

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
        let id = PallasFr::rand(&mut rng);
        let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id.clone());
        account.balance = 50;

        let account_tree = get_tree_with_account_comm::<L>(
            &account,
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();

        let deposit_amount = 25;
        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_deposit(deposit_amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        let (proof, nullifier) = DepositProof::new(
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
            .verify(
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
            assert_eq!(proof.0.encrypted_pubkeys.decrypt(i, sk.0), account_pk.0);
        }

        assert!(
            proof
                .verify(
                    asset_id,
                    deposit_amount + 5,
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
                .is_err()
        );

        assert!(
            proof
                .verify(
                    asset_id,
                    deposit_amount,
                    updated_account_comm,
                    PallasA::rand(&mut rng),
                    auditor_pubkeys.clone(),
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    enc_key_gen,
                    &mut rng,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    asset_id + 1,
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
                .is_err()
        );
    }

    #[test]
    fn batch_withdraw_proofs() {
        let mut rng = rand::thread_rng();

        const NUM_GENS: usize = 1 << 13;
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, _) =
            setup_gens::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let withdraw_amount = 30;
        let batch_size = 10;

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
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id);
            account.balance = 100;
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
            let (proof, nullifier) = WithdrawProof::new(
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
                .verify(
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
                .verify_and_return_tuples(
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

        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

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
                .verify_and_return_tuples(
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
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, _) =
            setup_gens::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let withdraw_amount = 30;
        let batch_size = 10;

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
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id);
            account.balance = 100;
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
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let (proof, nullifier) = WithdrawProof::new_with_given_prover(
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
                .verify_sigma_protocols_and_enforce_constraints(
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
                .verify_sigma_protocols_and_enforce_constraints(
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
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, _) =
            setup_gens::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let deposit_amount = 25;
        let batch_size = 10;

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
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id);
            account.balance = 50;
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
            let (proof, nullifier) = DepositProof::new(
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
                .verify(
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
                .verify_and_return_tuples(
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

        batch_verify_bp(even_tuples, odd_tuples, &account_tree_params).unwrap();

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
                .verify_and_return_tuples(
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
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
        const L: usize = 512;
        let (account_tree_params, account_comm_key, enc_key_gen, _) =
            setup_gens::<NUM_GENS>(b"testing");

        let asset_id = 1;
        let deposit_amount = 25;
        let batch_size = 10;

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
            let id = PallasFr::rand(&mut rng);
            let (mut account, _, _) = new_account(&mut rng, asset_id, sk, id);
            account.balance = 50;
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
            &account_tree_params.even_parameters.pc_gens,
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens, odd_transcript);

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);
        for i in 0..batch_size {
            let (proof, nullifier) = DepositProof::new_with_given_prover(
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
                .verify_sigma_protocols_and_enforce_constraints(
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
                .verify_sigma_protocols_and_enforce_constraints(
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
            &account_tree_params,
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(&rmc_0, &rmc_1).unwrap();
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
}
