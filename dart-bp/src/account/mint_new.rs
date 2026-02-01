use crate::account::common::{ensure_correct_balance_change, ensure_same_accounts};
use crate::account::state::NUM_GENERATORS;
use crate::account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment};
use crate::util::{
    bp_gens_for_vec_commitment, enforce_constraints_for_randomness_relations,
    prove_with_rng, verify_with_rng, BPProof,
};
use crate::{
    ASSET_ID_LABEL, Error, ID_LABEL, INCREASE_BAL_BY_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL,
    ROOT_LABEL, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL,
    UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript, error::Result,
};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::parameters::{SelRerandProofParametersNew};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol};
use schnorr_pok::partial::{PartialPokDiscreteLog, PartialSchnorrResponse};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;
use ark_ec_divisors::DivisorCurve;
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use bulletproofs::{BulletproofGens, PedersenGens};

pub const ISSUER_PK_LABEL: &'static [u8; 9] = b"issuer_pk";

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MintTxnProofNew<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub r1cs_proof: BPProof<G0, G1>,
    /// This contains the old account state, but re-randomized (as re-randomized leaf)
    pub re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
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
> MintTxnProofNew<L, F0, F1, G0, G1>
{
    /// `issuer_pk` has the same secret key as the one in `account`
    pub fn new<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        issuer_pk: Affine<G0>,
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

        Self::new_with_given_transcript::<_, D0, D1, Parameters0, Parameters1>(
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

    pub fn new_with_given_transcript<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        issuer_pk: Affine<G0>,
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

        let (re_randomized_path, mut rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<R, D0, D1, Parameters0, Parameters1>(
                &mut even_prover,
                &mut odd_prover,
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
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params.even_parameters.sl_params.pc_gens().B_blinding),
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
            &Self::acc_new_gens(account_comm_key.clone()),
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
            account_tree_params.even_parameters.bp_gens(),
        );
        enforce_constraints_for_randomness_relations(&mut even_prover, vars);

        let mut transcript = even_prover.transcript();

        let t_bp = SchnorrCommitment::new(
            &Self::bp_gens_vec(account_tree_params.even_parameters.pc_gens(), account_tree_params.even_parameters.bp_gens()),
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
            prove_with_rng(even_prover, odd_prover, &account_tree_params.even_parameters.bp_gens(), &account_tree_params.odd_parameters.bp_gens(), rng)?;

        Ok((
            Self {
                r1cs_proof: BPProof {
                    even_proof,
                    odd_proof,
                },
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

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_pk: Affine<G0>,
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

    pub fn verify_with_given_transcript<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        issuer_pk: Affine<G0>,
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

        let mut even_verifier = Verifier::new(transcript_even);
        let mut odd_verifier = Verifier::new(transcript_odd);

        self.re_randomized_path
            .select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
                root,
                &mut even_verifier,
                &mut odd_verifier,
                account_tree_params,
            )?;

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
        let y = self.re_randomized_path.path.get_rerandomized_leaf()
            - asset_id_comm
            - issuer_pk_proj
            - (account_comm_key.id_gen() * id);
        self.resp_leaf.is_valid(
            &Self::leaf_gens(account_comm_key.clone(), account_tree_params.even_parameters.sl_params.pc_gens().B_blinding),
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
            &Self::bp_gens_vec(account_tree_params.even_parameters.pc_gens(), account_tree_params.even_parameters.bp_gens()),
            &self.comm_bp,
            &self.t_bp,
            &verifier_challenge,
            missing_resps,
        )?;

        Ok(verify_with_rng(
            even_verifier,
            odd_verifier,
            &self.r1cs_proof.even_proof,
            &self.r1cs_proof.odd_proof,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.odd_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?)
    }

    fn leaf_gens(
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        B_blinding: Affine<G0>,
    ) -> [Affine<G0>; NUM_GENERATORS - 2] {
        [
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            B_blinding,
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

    fn bp_gens_vec(pc_gens: &PedersenGens<Affine<G0>>, bp_gens: &BulletproofGens<Affine<G0>>) -> [Affine<G0>; 6] {
        let mut gens = bp_gens_for_vec_commitment(5, bp_gens);
        [
            pc_gens.B_blinding,
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
    use crate::account::tests::{get_tree_with_account_comm, setup_gens_new};
    use crate::account_registration::tests::new_account;
    use crate::keys::keygen_sig;
    use ark_ff::Field;
    use ark_std::UniformRand;
    use std::time::Instant;
    use ark_ec_divisors::curves::{
        pallas::PallasParams, pallas::Point as PallasPoint, vesta::Point as VestaPoint,
        vesta::VestaParams,
    };
    use ark_pallas::{Fr as PallasFr};

    #[test]
    fn increase_supply_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 12; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;

        // Issuer creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let id = PallasFr::rand(&mut rng);
        let (account, _, _) = new_account(&mut rng, asset_id, sk_i, id.clone());

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
        assert_eq!(updated_account.randomness, account.randomness.square());
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = MintTxnProofNew::new::<_, PallasPoint, VestaPoint, PallasParams, VestaParams>(
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
            .verify::<_, PallasParams, VestaParams>(
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

        println!("For mint txn");
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time,
            verifier_time
        );
    }
}