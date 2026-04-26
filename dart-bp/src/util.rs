use crate::account::common::leg_link::{LegAccountLink, LegAccountLinkProtocol};
use crate::account::state::{
    ASSET_ID_GEN_INDEX, AccountCommitmentKeyTrait, AccountState, BALANCE_GEN_INDEX,
    COUNTER_GEN_INDEX, CURRENT_RANDOMNESS_GEN_INDEX, CURRENT_RHO_GEN_INDEX, ID_GEN_INDEX,
    NUM_GENERATORS, RANDOMNESS_GEN_INDEX, RHO_GEN_INDEX, SK_ENC_INV_GEN_INDEX, SK_GEN_INDEX,
};
use crate::error::*;
use crate::leg::{AmountCiphertext, LegEncryptionCore, PartyEphemeralPublicKey};
use crate::{AssetId, BALANCE_BITS, Balance};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::marker::PhantomData;
use ark_std::string::ToString;
use ark_std::{format, vec, vec::Vec};
#[cfg(feature = "std")]
use bulletproofs::r1cs::batch_verify;
use bulletproofs::r1cs::{
    ConstraintSystem, LinearCombination, Prover, R1CSProof, Variable, VerificationTuple, Verifier,
    add_verification_tuple_to_rmc, add_verification_tuples_to_rmc as add_vts_to_rmc,
    batch_verify_with_rng, verify_given_verification_tuple,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use core::iter::Copied;
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::{SelRerandParametersRef, SelRerandProofParameters};
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_chacha::ChaChaRng;
use rand_core::{CryptoRng, CryptoRngCore, RngCore, SeedableRng};
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    PartialPokDiscreteLog, PartialPokPedersenCommitment, PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;

/// Re-seed an RNG to generate a new non-shared RNG.
///
/// This is useful when using the `parallel` feature to ensure that different threads have different RNGs.
pub fn reseed_rng<R: RngCore + CryptoRng>(rng: &mut R) -> ChaChaRng {
    let mut buf = [0_u8; 32];
    rng.fill_bytes(&mut buf);
    ChaChaRng::from_seed(buf)
}

/// Generate two ChaChaRngs (for even and odd levels) from a given RNG
pub fn generate_even_odd_rngs<R: RngCore + CryptoRng>(rng: &mut R) -> (ChaChaRng, ChaChaRng) {
    let rng_even = reseed_rng(rng);
    let rng_odd = reseed_rng(rng);
    (rng_even, rng_odd)
}

#[macro_export]
macro_rules! add_to_transcript {
    ($transcript:expr, $($label:expr, $value:expr),* $(,)?) => {
        let mut buf = ::ark_std::vec![];
        $(
            $value.serialize_compressed(&mut buf)?;
            $transcript.append($label, &buf);
        )*
        buf.clear()
    };
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BPProof<
    G0: SWCurveConfig + Clone + Copy,
    G1: SWCurveConfig<ScalarField = G0::BaseField, BaseField = G0::ScalarField> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
}

/// Creates two new transcripts and two new provers, one for even level and one for odd.
/// Also re-randomizes the path and enforces the corresponding constraints. Returns the even prover,
/// odd prover, re-randomize path and blinding used to re-randomize the leaf
pub fn initialize_curve_tree_prover<
    'g,
    R: CryptoRngCore,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    rng: &mut R,
    even_label: &'static [u8],
    odd_label: &'static [u8],
    leaf_path: CurveTreeWitnessPath<L, G0, G1>,
    tree_parameters: &'g SelRerandProofParameters<G0, G1>,
) -> (
    Prover<'g, MerlinTranscript, Affine<G0>>,
    Prover<'g, MerlinTranscript, Affine<G1>>,
    SelectAndRerandomizePath<L, G0, G1>,
    F0,
) {
    let even_transcript = MerlinTranscript::new(even_label);
    let odd_transcript = MerlinTranscript::new(odd_label);
    initialize_curve_tree_prover_with_given_transcripts(
        rng,
        leaf_path,
        tree_parameters,
        even_transcript,
        odd_transcript,
    )
}

/// Same as `initialize_curve_tree_prover` but accepts the transcripts for
/// even and odd levels rather than creating new
pub fn initialize_curve_tree_prover_with_given_transcripts<
    'g,
    R: CryptoRngCore,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    rng: &mut R,
    leaf_path: CurveTreeWitnessPath<L, G0, G1>,
    tree_parameters: &'g SelRerandProofParameters<G0, G1>,
    even_transcript: MerlinTranscript,
    odd_transcript: MerlinTranscript,
) -> (
    Prover<'g, MerlinTranscript, Affine<G0>>,
    Prover<'g, MerlinTranscript, Affine<G1>>,
    SelectAndRerandomizePath<L, G0, G1>,
    F0,
) {
    let mut even_prover = Prover::new(
        &tree_parameters.even_parameters.sl_params.pc_gens(),
        even_transcript,
    );
    let mut odd_prover = Prover::new(
        &tree_parameters.odd_parameters.sl_params.pc_gens(),
        odd_transcript,
    );

    let (re_randomized_path, rerandomization) = leaf_path.select_and_rerandomize_prover_gadget(
        &mut even_prover,
        &mut odd_prover,
        tree_parameters,
        rng,
    );

    (even_prover, odd_prover, re_randomized_path, rerandomization)
}

/// Creates two new transcripts and two new verifiers, one for even level and one for odd.
/// Adds the path commitments and enforces the corresponding constraints.
/// Returns the even verifier and odd verifier,
pub fn initialize_curve_tree_verifier<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_label: &'static [u8],
    odd_label: &'static [u8],
    re_randomized_path: &SelectAndRerandomizePath<L, G0, G1>,
    tree_root: &Root<L, 1, G0, G1>,
    tree_parameters: &SelRerandProofParameters<G0, G1>,
) -> (
    Verifier<MerlinTranscript, Affine<G0>>,
    Verifier<MerlinTranscript, Affine<G1>>,
) {
    let even_transcript = MerlinTranscript::new(even_label);
    let odd_transcript = MerlinTranscript::new(odd_label);
    initialize_curve_tree_verifier_with_given_transcripts(
        re_randomized_path,
        tree_root,
        tree_parameters,
        even_transcript,
        odd_transcript,
    )
}

/// Same as `initialize_curve_tree_verifier` but accepts the transcripts for
/// even and odd levels rather than creating new
pub fn initialize_curve_tree_verifier_with_given_transcripts<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    re_randomized_path: &SelectAndRerandomizePath<L, G0, G1>,
    tree_root: &Root<L, 1, G0, G1>,
    tree_parameters: &SelRerandProofParameters<G0, G1>,
    even_transcript: MerlinTranscript,
    odd_transcript: MerlinTranscript,
) -> (
    Verifier<MerlinTranscript, Affine<G0>>,
    Verifier<MerlinTranscript, Affine<G1>>,
) {
    let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
    let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

    let _ = re_randomized_path.select_and_rerandomize_verifier_gadget(
        tree_root,
        &mut even_verifier,
        &mut odd_verifier,
        tree_parameters,
    );

    (even_verifier, odd_verifier)
}

/// Enforce that balance has correctly changed. If `has_balance_decreased` is true, then `old_bal - new_bal = amount` else `new_bal - old_bal = amount`
pub fn enforce_balance_change_prover<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    old_bal: Balance,
    new_bal: Balance,
    amount: Vec<Balance>,
    has_balance_decreased: Vec<bool>,
    even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
) -> Result<(F0, Affine<G0>)> {
    // Commit to amount, old and new balance
    let comm_bp_bal_blinding = F0::rand(rng);
    let mut amounts = amount.into_iter().map(|a| F0::from(a)).collect::<Vec<_>>();
    amounts.push(F0::from(old_bal));
    amounts.push(F0::from(new_bal));
    let (comm_bp_bal, vars) = even_prover.commit_vec(&amounts, comm_bp_bal_blinding, bp_gens);
    enforce_constraints_for_balance_change(
        even_prover,
        vars,
        has_balance_decreased,
        Some(new_bal),
    )?;
    Ok((comm_bp_bal_blinding, comm_bp_bal))
}

/// Enforce that balance has correctly changed. If `has_balance_decreased` is true, then `old_bal - new_bal = amount` else `new_bal - old_bal = amount`
pub fn enforce_balance_change_verifier<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0>>(
    comm_bp_bal: Affine<G0>,
    has_balance_decreased: Vec<bool>,
    even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
) -> Result<()> {
    let num_vars = has_balance_decreased.len() + 2; // amounts + old_balance + new_balance
    let vars = even_verifier.commit_vec(num_vars, comm_bp_bal);

    enforce_constraints_for_balance_change(even_verifier, vars, has_balance_decreased, None)?;

    Ok(())
}

pub fn enforce_constraints_for_balance_change<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut committed_variables: Vec<Variable<F>>,
    has_balance_decreased: Vec<bool>,
    new_bal: Option<Balance>,
) -> Result<()> {
    let var_amount = committed_variables
        .drain(0..has_balance_decreased.len())
        .collect::<Vec<_>>();
    let var_bal_new = committed_variables.pop().unwrap();
    let var_bal_old = committed_variables.pop().unwrap();
    debug_assert!(committed_variables.is_empty());
    let mut delta = LinearCombination::default();
    for (i, b) in has_balance_decreased.into_iter().enumerate() {
        if b {
            delta = delta - var_amount[i];
        } else {
            delta = delta + var_amount[i];
        }
    }

    cs.constrain(var_bal_old + delta - var_bal_new);
    // new balance does not overflow
    range_proof(
        cs,
        var_bal_new.into(),
        new_bal.map(|a| a as u128),
        BALANCE_BITS.into(),
    )?;
    Ok(())
}

/// Generate responses (Schnorr step 3) for state change just related to amount and balances
pub fn generate_schnorr_responses_for_balance_change<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    amount: Vec<Balance>,
    comm_bp_bal_blinding: G0::ScalarField,
    t_comm_bp_bal: SchnorrCommitment<Affine<G0>>,
    t_leg_amount: Vec<PokPedersenCommitmentProtocol<Affine<G0>>>,
    prover_challenge: &F0,
) -> Result<(
    PartialSchnorrResponse<Affine<G0>>,
    Vec<PartialPokPedersenCommitment<Affine<G0>>>,
)> {
    if t_leg_amount.len() != amount.len() {
        return Err(Error::ProofGenerationError(format!(
            "Balance-change response generation: t_leg_amount.len() ({}) != amount.len() ({})",
            t_leg_amount.len(),
            amount.len()
        )));
    }

    let mut wits = BTreeMap::new();
    wits.insert(0, comm_bp_bal_blinding);
    for (i, amount) in amount.into_iter().enumerate() {
        wits.insert(i + 1, F0::from(amount));
    }

    // Response for other witnesses will already be generated in sigma protocols for leaf and account commitment
    let resp_comm_bp_bal = t_comm_bp_bal.partial_response(wits, prover_challenge)?;

    // Response for witnesses will already be generated in sigma protocol for leaf and Bulletproof commitment
    let mut resp_leg_amount = Vec::with_capacity(t_leg_amount.len());
    for t_leg_amount in t_leg_amount {
        resp_leg_amount.push(t_leg_amount.gen_partial_proof());
    }
    Ok((resp_comm_bp_bal, resp_leg_amount))
}

#[cfg(feature = "std")]
pub fn prove<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_prover: Prover<MerlinTranscript, Affine<G0>>,
    odd_prover: Prover<MerlinTranscript, Affine<G1>>,
    even_bp_gens: &BulletproofGens<Affine<G0>>,
    odd_bp_gens: &BulletproofGens<Affine<G1>>,
) -> Result<(R1CSProof<Affine<G0>>, R1CSProof<Affine<G1>>)> {
    let mut rng = rand::thread_rng();
    prove_with_rng(even_prover, odd_prover, even_bp_gens, odd_bp_gens, &mut rng)
}

#[allow(unused_variables)]
pub fn prove_with_rng<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_prover: Prover<MerlinTranscript, Affine<G0>>,
    odd_prover: Prover<MerlinTranscript, Affine<G1>>,
    even_bp_gens: &BulletproofGens<Affine<G0>>,
    odd_bp_gens: &BulletproofGens<Affine<G1>>,
    rng: &mut R,
) -> Result<(R1CSProof<Affine<G0>>, R1CSProof<Affine<G1>>)> {
    let (mut rng_even, mut rng_odd) = generate_even_odd_rngs(rng);

    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || even_prover.prove_with_rng(even_bp_gens, &mut rng_even),
        || odd_prover.prove_with_rng(odd_bp_gens, &mut rng_odd),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover.prove_with_rng(even_bp_gens, &mut rng_even),
        odd_prover.prove_with_rng(odd_bp_gens, &mut rng_odd),
    );

    let (even_proof, odd_proof) = (even_proof?, odd_proof?);
    Ok((even_proof, odd_proof))
}

#[cfg(feature = "std")]
pub fn verify<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
    odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
    even_proof: &R1CSProof<Affine<G0>>,
    odd_proof: &R1CSProof<Affine<G1>>,
    even_pc_gens: &PedersenGens<Affine<G0>>,
    odd_pc_gens: &PedersenGens<Affine<G1>>,
    even_bp_gens: &BulletproofGens<Affine<G0>>,
    odd_bp_gens: &BulletproofGens<Affine<G1>>,
) -> Result<()> {
    let mut rng = rand::thread_rng();
    verify_with_rng(
        even_verifier,
        odd_verifier,
        even_proof,
        odd_proof,
        even_pc_gens,
        odd_pc_gens,
        even_bp_gens,
        odd_bp_gens,
        &mut rng,
    )
}

#[allow(unused_variables)]
pub fn verify_with_rng<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
    odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
    even_proof: &R1CSProof<Affine<G0>>,
    odd_proof: &R1CSProof<Affine<G1>>,
    even_pc_gens: &PedersenGens<Affine<G0>>,
    odd_pc_gens: &PedersenGens<Affine<G1>>,
    even_bp_gens: &BulletproofGens<Affine<G0>>,
    odd_bp_gens: &BulletproofGens<Affine<G1>>,
    rng: &mut R,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || even_verifier.verify(even_proof, even_pc_gens, even_bp_gens),
        || odd_verifier.verify(odd_proof, odd_pc_gens, odd_bp_gens),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        even_verifier.verify_with_rng(even_proof, even_pc_gens, even_bp_gens, rng),
        odd_verifier.verify_with_rng(odd_proof, odd_pc_gens, odd_bp_gens, rng),
    );

    even_res?;
    odd_res?;

    Ok(())
}

#[allow(unused_variables)]
pub fn get_verification_tuples_with_rng<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
    odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
    even_proof: &R1CSProof<Affine<G0>>,
    odd_proof: &R1CSProof<Affine<G1>>,
    rng: &mut R,
) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || even_verifier.verification_scalars_and_points(even_proof),
        || odd_verifier.verification_scalars_and_points(odd_proof),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        even_verifier.verification_scalars_and_points_with_rng(even_proof, rng),
        odd_verifier.verification_scalars_and_points_with_rng(odd_proof, rng),
    );

    let even = even_res?;
    let odd = odd_res?;

    Ok((even, odd))
}

/// Verify given verification tuples and return error if either verification fails
pub fn verify_given_verification_tuples<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    P: SelRerandParametersRef<G0, G1>,
>(
    even_tuple: VerificationTuple<Affine<G0>>,
    odd_tuple: VerificationTuple<Affine<G1>>,
    tree_params: &P,
) -> Result<()> {
    let even_pc_gens = tree_params.even_parameters().pc_gens();
    let odd_pc_gens = tree_params.odd_parameters().pc_gens();
    let even_bp_gens = tree_params.even_parameters().bp_gens();
    let odd_bp_gens = tree_params.odd_parameters().bp_gens();

    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || verify_given_verification_tuple(even_tuple, even_pc_gens, even_bp_gens),
        || verify_given_verification_tuple(odd_tuple, odd_pc_gens, odd_bp_gens),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        verify_given_verification_tuple(even_tuple, even_pc_gens, even_bp_gens),
        verify_given_verification_tuple(odd_tuple, odd_pc_gens, odd_bp_gens),
    );

    even_res?;
    odd_res?;

    Ok(())
}

/// Add bulletproof verification tuples to RandomizedMultChecker
pub fn add_verification_tuples_to_rmc<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    P: SelRerandParametersRef<G0, G1>,
>(
    even_tuple: VerificationTuple<Affine<G0>>,
    odd_tuple: VerificationTuple<Affine<G1>>,
    tree_params: &P,
    rmc_0: &mut RandomizedMultChecker<Affine<G0>>,
    rmc_1: &mut RandomizedMultChecker<Affine<G1>>,
) -> Result<()> {
    let even_params = tree_params.even_parameters();
    let odd_params = tree_params.odd_parameters();
    let even_pc_gens = even_params.pc_gens();
    let odd_pc_gens = odd_params.pc_gens();
    let even_bp_gens = even_params.bp_gens();
    let odd_bp_gens = odd_params.bp_gens();

    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || add_verification_tuple_to_rmc(even_tuple, even_pc_gens, even_bp_gens, rmc_0),
        || add_verification_tuple_to_rmc(odd_tuple, odd_pc_gens, odd_bp_gens, rmc_1),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        add_verification_tuple_to_rmc(even_tuple, even_pc_gens, even_bp_gens, rmc_0),
        add_verification_tuple_to_rmc(odd_tuple, odd_pc_gens, odd_bp_gens, rmc_1),
    );

    even_res.map_err(Error::from)?;
    odd_res.map_err(Error::from)?;

    Ok(())
}

/// Verify bulletproof verification tuples using RandomizedMultChecker and return error if either verification fails
pub fn verify_rmc<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    rmc_0: RandomizedMultChecker<Affine<G0>>,
    rmc_1: RandomizedMultChecker<Affine<G1>>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_verify, odd_verify) = rayon::join(|| rmc_0.verify(), || rmc_1.verify());

    #[cfg(not(feature = "parallel"))]
    let (even_verify, odd_verify) = (rmc_0.verify(), rmc_1.verify());

    even_verify.map_err(|_| {
        Error::ProofVerificationError("RandomizedMultChecker even verification failed".to_string())
    })?;
    odd_verify.map_err(|_| {
        Error::ProofVerificationError("RandomizedMultChecker odd verification failed".to_string())
    })?;

    Ok(())
}

#[cfg(feature = "std")]
pub fn batch_verify_bp<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_tuples: Vec<VerificationTuple<Affine<G0>>>,
    odd_tuples: Vec<VerificationTuple<Affine<G1>>>,
    even_pc_gens: &PedersenGens<Affine<G0>>,
    odd_pc_gens: &PedersenGens<Affine<G1>>,
    even_bp_gens: &BulletproofGens<Affine<G0>>,
    odd_bp_gens: &BulletproofGens<Affine<G1>>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || batch_verify(even_tuples, even_pc_gens, even_bp_gens),
        || batch_verify(odd_tuples, odd_pc_gens, odd_bp_gens),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        batch_verify(even_tuples, even_pc_gens, even_bp_gens),
        batch_verify(odd_tuples, odd_pc_gens, odd_bp_gens),
    );

    even_res?;
    odd_res?;

    Ok(())
}

pub fn batch_verify_bp_with_rng<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_tuples: Vec<VerificationTuple<Affine<G0>>>,
    odd_tuples: Vec<VerificationTuple<Affine<G1>>>,
    even_pc_gens: &PedersenGens<Affine<G0>>,
    odd_pc_gens: &PedersenGens<Affine<G1>>,
    even_bp_gens: &BulletproofGens<Affine<G0>>,
    odd_bp_gens: &BulletproofGens<Affine<G1>>,
    rng: &mut R,
) -> Result<()> {
    let (mut rng_even, mut rng_odd) = generate_even_odd_rngs(rng);

    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || batch_verify_with_rng(even_tuples, even_pc_gens, even_bp_gens, &mut rng_even),
        || batch_verify_with_rng(odd_tuples, odd_pc_gens, odd_bp_gens, &mut rng_odd),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        batch_verify_with_rng(even_tuples, even_pc_gens, even_bp_gens, &mut rng_even),
        batch_verify_with_rng(odd_tuples, odd_pc_gens, odd_bp_gens, &mut rng_odd),
    );

    even_res?;
    odd_res?;

    Ok(())
}

pub fn add_verification_tuples_batches_to_rmc<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_tuples: Vec<VerificationTuple<Affine<G0>>>,
    odd_tuples: Vec<VerificationTuple<Affine<G1>>>,
    even_pc_gens: &PedersenGens<Affine<G0>>,
    odd_pc_gens: &PedersenGens<Affine<G1>>,
    even_bp_gens: &BulletproofGens<Affine<G0>>,
    odd_bp_gens: &BulletproofGens<Affine<G1>>,
    rmc_0: &mut RandomizedMultChecker<Affine<G0>>,
    rmc_1: &mut RandomizedMultChecker<Affine<G1>>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || add_vts_to_rmc(even_tuples, even_pc_gens, even_bp_gens, rmc_0),
        || add_vts_to_rmc(odd_tuples, odd_pc_gens, odd_bp_gens, rmc_1),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        add_vts_to_rmc(even_tuples, even_pc_gens, even_bp_gens, rmc_0),
        add_vts_to_rmc(odd_tuples, odd_pc_gens, odd_bp_gens, rmc_1),
    );

    even_res?;
    odd_res?;

    Ok(())
}

/// Create the Schnorr T-values for the account commitments (old re-randomized leaf and new account).
///
/// When `include_sk` is true (solo mode), the generators include `sk_gen` and `sk_enc_gen`
/// and the blinding vectors include `sk_blinding` and `sk_enc_blinding`.
/// When `include_sk` is false (W2/W3 host mode), those generators and blindings are excluded.
pub(crate) fn create_account_commitment_t_values<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Copy,
>(
    rng: &mut R,
    include_sk: bool,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    b_blinding: Affine<G0>,
    is_asset_id_revealed: bool,
    // SK-related (only used when include_sk=true)
    sk_blinding: Option<F0>,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    old_counter_blinding: F0,
    asset_id_blinding: Option<F0>,
    initial_rho_blinding: F0,
    old_rho_blinding: F0,
    new_rho_blinding: F0,
    initial_randomness_blinding: F0,
    old_randomness_blinding: F0,
    new_randomness_blinding: F0,
    id_blinding: F0,
    // SK-related (only used when include_sk=true)
    sk_enc_blinding: Option<F0>,
) -> (SchnorrCommitment<Affine<G0>>, SchnorrCommitment<Affine<G0>>) {
    let b_blinding_rerandomization = F0::rand(rng);

    match (is_asset_id_revealed, include_sk) {
        // Asset-id hidden, with sk
        (false, true) => {
            let asset_id_blinding = asset_id_blinding.unwrap();
            let sk_blinding = sk_blinding.unwrap();
            let sk_enc_blinding = sk_enc_blinding.unwrap();
            let t_acc_old = SchnorrCommitment::new(
                &account_comm_key.as_gens_with_blinding(b_blinding),
                vec![
                    sk_blinding,
                    old_balance_blinding,
                    old_counter_blinding,
                    asset_id_blinding,
                    initial_rho_blinding,
                    old_rho_blinding,
                    initial_randomness_blinding,
                    old_randomness_blinding,
                    id_blinding,
                    sk_enc_blinding,
                    b_blinding_rerandomization,
                ],
            );
            let t_acc_new = SchnorrCommitment::new(
                &account_comm_key.as_gens(),
                vec![
                    sk_blinding,
                    new_balance_blinding,
                    old_counter_blinding,
                    asset_id_blinding,
                    initial_rho_blinding,
                    new_rho_blinding,
                    initial_randomness_blinding,
                    new_randomness_blinding,
                    id_blinding,
                    sk_enc_blinding,
                ],
            );
            (t_acc_old, t_acc_new)
        }
        // Asset-id revealed, with sk
        (true, true) => {
            let sk_blinding = sk_blinding.unwrap();
            let sk_enc_blinding = sk_enc_blinding.unwrap();
            let t_acc_old = SchnorrCommitment::new(
                &account_comm_key.as_gens_with_blinding_and_asset_id_revealed(b_blinding),
                vec![
                    sk_blinding,
                    old_balance_blinding,
                    old_counter_blinding,
                    initial_rho_blinding,
                    old_rho_blinding,
                    initial_randomness_blinding,
                    old_randomness_blinding,
                    id_blinding,
                    sk_enc_blinding,
                    b_blinding_rerandomization,
                ],
            );
            let t_acc_new = SchnorrCommitment::new(
                &account_comm_key.as_gens_with_asset_id_revealed(),
                vec![
                    sk_blinding,
                    new_balance_blinding,
                    old_counter_blinding,
                    initial_rho_blinding,
                    new_rho_blinding,
                    initial_randomness_blinding,
                    new_randomness_blinding,
                    id_blinding,
                    sk_enc_blinding,
                ],
            );
            (t_acc_old, t_acc_new)
        }
        // Asset-id hidden, without sk
        (false, false) => {
            let asset_id_blinding = asset_id_blinding.unwrap();
            let t_acc_old = SchnorrCommitment::new(
                &account_comm_key.as_gens_with_blinding_without_sk(b_blinding),
                vec![
                    old_balance_blinding,
                    old_counter_blinding,
                    asset_id_blinding,
                    initial_rho_blinding,
                    old_rho_blinding,
                    initial_randomness_blinding,
                    old_randomness_blinding,
                    id_blinding,
                    b_blinding_rerandomization,
                ],
            );
            let mut new_gens = account_comm_key.as_gens_without_sk().to_vec();
            new_gens.push(b_blinding);
            let t_acc_new = SchnorrCommitment::new(
                &new_gens,
                vec![
                    new_balance_blinding,
                    old_counter_blinding,
                    asset_id_blinding,
                    initial_rho_blinding,
                    new_rho_blinding,
                    initial_randomness_blinding,
                    new_randomness_blinding,
                    id_blinding,
                    F0::rand(rng),
                ],
            );
            (t_acc_old, t_acc_new)
        }
        // Asset-id revealed, without sk
        (true, false) => {
            let t_acc_old = SchnorrCommitment::new(
                &account_comm_key.as_gens_with_blinding_without_sk_and_asset_id(b_blinding),
                vec![
                    old_balance_blinding,
                    old_counter_blinding,
                    initial_rho_blinding,
                    old_rho_blinding,
                    initial_randomness_blinding,
                    old_randomness_blinding,
                    id_blinding,
                    b_blinding_rerandomization,
                ],
            );
            let mut new_gens = account_comm_key.as_gens_without_sk_and_asset_id().to_vec();
            new_gens.push(b_blinding);
            let t_acc_new = SchnorrCommitment::new(
                &new_gens,
                vec![
                    new_balance_blinding,
                    old_counter_blinding,
                    initial_rho_blinding,
                    new_rho_blinding,
                    initial_randomness_blinding,
                    new_randomness_blinding,
                    id_blinding,
                    F0::rand(rng),
                ],
            );
            (t_acc_old, t_acc_new)
        }
    }
}

/// Create the BP commitment, enforce constraints, and create Schnorr T-values for the BP
/// commitment and nullifier.
///
/// When `include_sk` is true (solo mode), the BP commitment includes `sk_enc` and `sk_enc_inv`
/// (8 variables) and enforces both `sk_enc * sk_enc_inv = 1` and randomness relation constraints.
/// When `include_sk` is false (W2/W3 host mode), the BP commitment has only 6 variables
/// (rho/randomness relations) and enforces only randomness relation constraints.
pub(crate) fn create_bp_and_null_t_values<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Copy,
>(
    rng: &mut R,
    include_sk: bool,
    // BP witness values
    initial_rho: F0,
    old_rho: F0,
    new_rho: F0,
    initial_randomness: F0,
    old_randomness: F0,
    new_randomness: F0,
    initial_rho_blinding: F0,
    old_rho_blinding: F0,
    new_rho_blinding: F0,
    initial_randomness_blinding: F0,
    old_randomness_blinding: F0,
    new_randomness_blinding: F0,
    // SK-related (only used when include_sk=true)
    sk_enc: Option<F0>,
    sk_enc_blinding: Option<F0>,
    sk_enc_inv_blinding: Option<F0>,
    prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
) -> Result<(
    Affine<G0>,                         // nullifier
    Affine<G0>,                         // comm_bp
    F0,                                 // comm_bp_blinding
    PokDiscreteLogProtocol<Affine<G0>>, // t_null
    SchnorrCommitment<Affine<G0>>,      // t_bp
)> {
    let null_gen = account_comm_key.current_rho_gen();
    let nullifier = (null_gen * old_rho).into_affine();
    let t_null = PokDiscreteLogProtocol::init(old_rho, old_rho_blinding, &null_gen);

    let comm_bp_blinding = F0::rand(rng);

    let mut wits = vec![
        initial_rho,
        old_rho,
        new_rho,
        initial_randomness,
        old_randomness,
        new_randomness,
    ];
    let mut blindings = vec![
        F0::rand(rng), // for comm_bp_blinding
        initial_rho_blinding,
        old_rho_blinding,
        new_rho_blinding,
        initial_randomness_blinding,
        old_randomness_blinding,
        new_randomness_blinding,
    ];

    let r = if include_sk {
        let sk_enc = sk_enc.unwrap();
        let sk_enc_inv = sk_enc.inverse().ok_or(Error::InvertingZero)?;
        wits.push(sk_enc);
        wits.push(sk_enc_inv);
        blindings.push(sk_enc_blinding.unwrap());
        blindings.push(sk_enc_inv_blinding.unwrap());

        let (comm_bp, mut vars) = prover.commit_vec(&wits, comm_bp_blinding, bp_gens);
        enforce_constraints_for_sk_enc_relation(prover, &mut vars);
        enforce_constraints_for_randomness_relations(prover, &mut vars);

        let t_bp = SchnorrCommitment::new(
            &bp_gens_vec_for_randomness_and_sk_enc_relations(pc_gens, bp_gens),
            blindings,
        );
        (nullifier, comm_bp, comm_bp_blinding, t_null, t_bp)
    } else {
        let (comm_bp, mut vars) = prover.commit_vec(&wits, comm_bp_blinding, bp_gens);
        enforce_constraints_for_randomness_relations(prover, &mut vars);

        let t_bp = SchnorrCommitment::new(
            &bp_gens_vec_for_randomness_relations(pc_gens, bp_gens),
            blindings,
        );
        (nullifier, comm_bp, comm_bp_blinding, t_null, t_bp)
    };

    Zeroize::zeroize(&mut wits);
    Ok(r)
}

/// Create the leg-link T-values (participant ciphertext + asset-id ciphertext proofs).
/// Solo mode only — in W2/W3 host mode, leg-link proofs are created by the auth device.
pub(crate) fn create_leg_link_t_values<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Copy,
>(
    legs: &[(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )],
    sk_enc_inv: F0,
    sk_enc: F0,
    sk_enc_inv_blinding: F0,
    sk_enc_blinding: F0,
    asset_id: AssetId,
    asset_id_blinding: Option<F0>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
) -> Vec<LegAccountLinkProtocol<G0>> {
    let mut t_leg_link = Vec::with_capacity(legs.len());

    for (core, party_eph_pk) in legs {
        let eph_pk_participant = party_eph_pk.eph_pk_participant();
        let t_participant = PokPedersenCommitmentProtocol::init(
            sk_enc_inv,
            sk_enc_inv_blinding,
            &eph_pk_participant,
            sk_enc,
            sk_enc_blinding,
            &enc_key_gen,
        );

        match asset_id_blinding {
            Some(asset_id_blinding) => {
                let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();
                let t_asset_id = PokPedersenCommitmentProtocol::init(
                    sk_enc_inv,
                    sk_enc_inv_blinding,
                    &eph_pk_base,
                    F0::from(asset_id),
                    asset_id_blinding,
                    &enc_gen,
                );
                t_leg_link.push(LegAccountLinkProtocol::AssetIdHidden {
                    t_participant,
                    t_asset_id,
                });
            }
            None => {
                if !core.is_asset_id_revealed() {
                    let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();
                    let t_asset_id =
                        PokDiscreteLogProtocol::init(sk_enc_inv, sk_enc_inv_blinding, &eph_pk_base);
                    t_leg_link.push(LegAccountLinkProtocol::AssetIdRevealedElsewhere {
                        t_participant,
                        t_asset_id,
                    });
                } else {
                    t_leg_link.push(LegAccountLinkProtocol::AssetIdRevealed { t_participant });
                }
            }
        }
    }

    t_leg_link
}

/// Add challenge contributions for leg-link T-values to the transcript.
pub(crate) fn add_leg_link_challenge_contributions<G0: SWCurveConfig + Copy>(
    legs: &[(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )],
    t_leg_link: &[LegAccountLinkProtocol<G0>],
    is_asset_id_revealed: bool,
    h_at: Option<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
    transcript: &mut MerlinTranscript,
) -> Result<()> {
    for (i, (core, party_eph_pk)) in legs.iter().enumerate() {
        let is_sender = party_eph_pk.is_sender();
        let eph_pk_participant = party_eph_pk.eph_pk_participant();
        let ct_participant = core.ct_participant(is_sender);

        t_leg_link[i].t_participant().challenge_contribution(
            &eph_pk_participant,
            &enc_key_gen,
            &ct_participant,
            &mut *transcript,
        )?;

        if is_asset_id_revealed {
            if !core.is_asset_id_revealed() {
                let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();
                let y = core.asset_id_ciphertext().as_ref().unwrap().into_group()
                    - h_at.unwrap().into_group();
                t_leg_link[i]
                    .t_asset_id_dl()
                    .unwrap()
                    .challenge_contribution(&eph_pk_base, &y.into_affine(), &mut *transcript)?;
            }
        } else {
            let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();
            t_leg_link[i]
                .t_asset_id_pc()
                .unwrap()
                .challenge_contribution(
                    &eph_pk_base,
                    &enc_gen,
                    &core.asset_id_ciphertext().unwrap(),
                    &mut *transcript,
                )?;
        }
    }
    Ok(())
}

/// Generate commitment to randomness (Sigma protocol step 1) for state change excluding changes related to amount and balances
pub(crate) fn generate_sigma_t_values_for_common_state_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Copy,
>(
    rng: &mut R,
    legs: Vec<(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )>,
    sk_enc: G0::ScalarField,
    old_account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    mut id_blinding: F0,
    mut sk_blinding: F0,
    mut old_balance_blinding: F0,
    mut new_balance_blinding: F0,
    mut old_counter_blinding: F0,
    mut initial_rho_blinding: F0,
    mut old_rho_blinding: F0,
    mut new_rho_blinding: F0,
    mut initial_randomness_blinding: F0,
    mut old_randomness_blinding: F0,
    mut new_randomness_blinding: F0,
    mut asset_id_blinding: Option<F0>,
    mut sk_enc_blinding: F0,
    mut sk_enc_inv_blinding: F0,
    prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
) -> Result<(
    Affine<G0>,
    Affine<G0>,
    F0,
    SchnorrCommitment<Affine<G0>>,
    SchnorrCommitment<Affine<G0>>,
    PokDiscreteLogProtocol<Affine<G0>>,
    Vec<LegAccountLinkProtocol<G0>>,
    SchnorrCommitment<Affine<G0>>,
)> {
    if legs.len() == 0 {
        return Err(Error::ProofGenerationError(
            "Common state-change commitment generation: legs must not be empty".to_string(),
        ));
    }

    let is_asset_id_revealed = asset_id_blinding.is_none();

    let mut sk_enc_inv = sk_enc.inverse().ok_or(Error::InvertingZero)?;

    let h_at = is_asset_id_revealed
        .then(|| (enc_gen * G0::ScalarField::from(old_account.asset_id())).into_affine());

    // Create account commitment T-values (with sk)
    let (t_acc_old, t_acc_new) = create_account_commitment_t_values(
        rng,
        true, // include_sk
        account_comm_key,
        pc_gens.B_blinding,
        is_asset_id_revealed,
        Some(sk_blinding),
        old_balance_blinding,
        new_balance_blinding,
        old_counter_blinding,
        asset_id_blinding,
        initial_rho_blinding,
        old_rho_blinding,
        new_rho_blinding,
        initial_randomness_blinding,
        old_randomness_blinding,
        new_randomness_blinding,
        id_blinding,
        Some(sk_enc_blinding),
    );

    // Create BP + null T-values (with sk)
    let (
        nullifier,
        comm_bp_randomness_relations,
        comm_bp_blinding,
        t_null,
        t_bp_randomness_relations,
    ) = create_bp_and_null_t_values(
        rng,
        true, // include_sk
        old_account.rho,
        old_account.current_rho,
        updated_account.current_rho,
        old_account.randomness,
        old_account.current_randomness,
        updated_account.current_randomness,
        initial_rho_blinding,
        old_rho_blinding,
        new_rho_blinding,
        initial_randomness_blinding,
        old_randomness_blinding,
        new_randomness_blinding,
        Some(sk_enc),
        Some(sk_enc_blinding),
        Some(sk_enc_inv_blinding),
        prover,
        account_comm_key,
        pc_gens,
        bp_gens,
    )?;

    // Create leg-link T-values (solo only)
    let t_leg_link = create_leg_link_t_values(
        &legs,
        sk_enc_inv,
        sk_enc,
        sk_enc_inv_blinding,
        sk_enc_blinding,
        old_account.asset_id(),
        asset_id_blinding,
        enc_key_gen,
        enc_gen,
    );

    Zeroize::zeroize(&mut id_blinding);
    Zeroize::zeroize(&mut sk_blinding);
    Zeroize::zeroize(&mut old_balance_blinding);
    Zeroize::zeroize(&mut new_balance_blinding);
    Zeroize::zeroize(&mut old_counter_blinding);
    Zeroize::zeroize(&mut initial_rho_blinding);
    Zeroize::zeroize(&mut old_rho_blinding);
    Zeroize::zeroize(&mut new_rho_blinding);
    Zeroize::zeroize(&mut old_randomness_blinding);
    Zeroize::zeroize(&mut new_randomness_blinding);
    Zeroize::zeroize(&mut initial_randomness_blinding);
    Zeroize::zeroize(&mut asset_id_blinding);
    Zeroize::zeroize(&mut sk_enc_blinding);
    Zeroize::zeroize(&mut sk_enc_inv_blinding);
    Zeroize::zeroize(&mut sk_enc_inv);

    let mut transcript = prover.transcript();

    // Add challenge contributions in solo transcript order
    t_acc_old.challenge_contribution(&mut transcript)?;
    t_acc_new.challenge_contribution(&mut transcript)?;
    t_bp_randomness_relations.challenge_contribution(&mut transcript)?;

    let null_gen = account_comm_key.current_rho_gen();
    t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript)?;

    add_leg_link_challenge_contributions(
        &legs,
        &t_leg_link,
        is_asset_id_revealed,
        h_at,
        enc_key_gen,
        enc_gen,
        &mut transcript,
    )?;

    Ok((
        nullifier,
        comm_bp_randomness_relations,
        comm_bp_blinding,
        t_acc_old,
        t_acc_new,
        t_null,
        t_leg_link,
        t_bp_randomness_relations,
    ))
}

/// Create the balance BP Schnorr commitment (t_comm_bp_bal).
/// The provided `amount_blindings` are shared with leg-amount proofs.
pub(crate) fn create_balance_bp_t_values<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    amount_blindings: Vec<F0>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
) -> SchnorrCommitment<Affine<G0>> {
    let num_amounts = amount_blindings.len();
    let mut gens = bp_gens_for_vec_commitment(2 + num_amounts as u32, bp_gens);
    let mut bases = Vec::with_capacity(3 + num_amounts);
    let mut blindings = Vec::with_capacity(3 + num_amounts);
    bases.push(pc_gens.B_blinding);
    blindings.push(F0::rand(rng));
    for b in amount_blindings {
        bases.push(gens.next().unwrap());
        blindings.push(b);
    }
    bases.push(gens.next().unwrap());
    bases.push(gens.next().unwrap());
    blindings.push(old_balance_blinding);
    blindings.push(new_balance_blinding);
    SchnorrCommitment::new(&bases, blindings)
}

/// Create leg-amount T-values (solo only).
/// Each t_leg_amount proves knowledge of sk_enc_inv and amount in the amount ciphertext.
pub(crate) fn create_leg_amount_t_values<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0>>(
    amounts: &[Balance],
    amount_blindings: Vec<F0>,
    sk_enc_inv: F0,
    sk_enc_inv_blinding: F0,
    eph_pk_amount: &[Affine<G0>],
    enc_gen: Affine<G0>,
) -> Vec<PokPedersenCommitmentProtocol<Affine<G0>>> {
    let mut t_leg_amount = Vec::with_capacity(amounts.len());
    for (i, b) in amount_blindings.into_iter().enumerate() {
        t_leg_amount.push(PokPedersenCommitmentProtocol::init(
            sk_enc_inv,
            sk_enc_inv_blinding,
            &eph_pk_amount[i],
            F0::from(amounts[i]),
            b,
            &enc_gen,
        ));
    }
    t_leg_amount
}

/// Add challenge contributions for leg-amount T-values to the transcript (solo only).
pub(crate) fn add_leg_amount_challenge_contributions<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    t_leg_amount: &[PokPedersenCommitmentProtocol<Affine<G0>>],
    eph_pk_amount: &[Affine<G0>],
    ct_amount: &[Affine<G0>],
    enc_gen: Affine<G0>,
    transcript: &mut MerlinTranscript,
) -> Result<()> {
    for i in 0..t_leg_amount.len() {
        t_leg_amount[i].challenge_contribution(
            &eph_pk_amount[i],
            &enc_gen,
            &ct_amount[i],
            &mut *transcript,
        )?;
    }
    Ok(())
}

/// Generate commitment to randomness (Sigma protocol step 1) for state change just related to amount and balances
pub(crate) fn generate_sigma_t_values_for_balance_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    amount: Vec<Balance>,
    ct_amount: Vec<Affine<G0>>,
    mut old_balance_blinding: F0,
    mut new_balance_blinding: F0,
    amount_blinding: Vec<F0>,
    mut sk_enc_inv: F0,
    mut sk_enc_inv_blinding: F0,
    eph_pk_amount: Vec<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_gen: Affine<G0>,
    mut prover_transcript: &mut MerlinTranscript,
) -> Result<(
    SchnorrCommitment<Affine<G0>>,
    Vec<PokPedersenCommitmentProtocol<Affine<G0>>>,
)> {
    if amount.len() != amount_blinding.len() {
        return Err(Error::ProofGenerationError(format!(
            "Balance-change commitment generation: amount.len() ({}) != amount_blinding.len() ({})",
            amount.len(),
            amount_blinding.len()
        )));
    }
    if ct_amount.len() != amount_blinding.len() {
        return Err(Error::ProofGenerationError(format!(
            "Balance-change commitment generation: ct_amount.len() ({}) != amount_blinding.len() ({})",
            ct_amount.len(),
            amount_blinding.len()
        )));
    }
    if ct_amount.len() != eph_pk_amount.len() {
        return Err(Error::ProofGenerationError(format!(
            "Balance-change commitment generation: ct_amount.len() ({}) != eph_pk_amount.len() ({})",
            ct_amount.len(),
            eph_pk_amount.len()
        )));
    }

    // Create balance BP Schnorr commitment (with shared amount blindings)
    let t_comm_bp_bal = create_balance_bp_t_values(
        rng,
        old_balance_blinding,
        new_balance_blinding,
        amount_blinding.clone(),
        pc_gens,
        bp_gens,
    );

    // Create leg-amount T-values (solo only)
    let t_leg_amount = create_leg_amount_t_values(
        &amount,
        amount_blinding,
        sk_enc_inv,
        sk_enc_inv_blinding,
        &eph_pk_amount,
        enc_gen,
    );

    Zeroize::zeroize(&mut old_balance_blinding);
    Zeroize::zeroize(&mut new_balance_blinding);
    Zeroize::zeroize(&mut sk_enc_inv);
    Zeroize::zeroize(&mut sk_enc_inv_blinding);

    // Add challenge contributions to the transcript
    t_comm_bp_bal.challenge_contribution(&mut prover_transcript)?;

    add_leg_amount_challenge_contributions(
        &t_leg_amount,
        &eph_pk_amount,
        &ct_amount,
        enc_gen,
        &mut prover_transcript,
    )?;

    Ok((t_comm_bp_bal, t_leg_amount))
}

/// Host version of [`generate_schnorr_responses_for_balance_change`].
/// Generates partial Schnorr response for the balance BP commitment.
/// No leg-amount responses (those belong to auth).
pub(crate) fn generate_host_sigma_responses_for_balance_change<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    amounts: &[Balance],
    comm_bp_bal_blinding: F0,
    t_comm_bp_bal: &SchnorrCommitment<Affine<G0>>,
    prover_challenge: &F0,
) -> Result<PartialSchnorrResponse<Affine<G0>>> {
    let mut wits = BTreeMap::new();
    wits.insert(0, comm_bp_bal_blinding);
    for (i, &amount) in amounts.iter().enumerate() {
        wits.insert(i + 1, F0::from(amount));
    }
    Ok(t_comm_bp_bal.partial_response(wits, prover_challenge)?)
}

/// Generate account commitment responses (Sigma protocol step 3).
///
/// When `include_sk` is true (solo mode), old witnesses include sk and sk_enc with
/// the leaf rerandomization blinding from b_blinding.
/// When `include_sk` is false (host mode), old witnesses exclude sk and sk_enc; the
/// last witness is the host's share of rerandomization.
pub(crate) fn generate_account_commitment_responses<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    t_acc_old: &SchnorrCommitment<Affine<G0>>,
    t_acc_new: &SchnorrCommitment<Affine<G0>>,
    is_asset_id_revealed: bool,
    include_sk: bool,
    // None for include_sk=false
    sk: Option<F0>,
    // None for include_sk=false
    sk_enc: Option<F0>,
    leaf_rerandomization: Option<F0>,
    // Host-related, None for include_sk=true
    host_rerandomization: Option<F0>,
    // Host's B_blinding witness for the new commitment (i.e. -rand_new_comm). Only for include_sk=false.
    host_new_b_blinding_witness: Option<F0>,
    prover_challenge: &F0,
) -> Result<(
    SchnorrResponse<Affine<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
)> {
    let mut old_wits: Vec<F0> = Vec::with_capacity(11);

    if include_sk {
        old_wits.push(sk.unwrap());
    }
    old_wits.push(account.balance.into());
    old_wits.push(account.counter.into());
    if !is_asset_id_revealed {
        old_wits.push(account.asset_id.into());
    }
    old_wits.push(account.rho);
    old_wits.push(account.current_rho);
    old_wits.push(account.randomness);
    old_wits.push(account.current_randomness);
    old_wits.push(account.id);
    if include_sk {
        old_wits.push(sk_enc.unwrap());
        old_wits.push(leaf_rerandomization.unwrap());
    } else {
        old_wits.push(host_rerandomization.unwrap());
    }

    let resp_acc_old = t_acc_old.response(&old_wits, prover_challenge)?;
    Zeroize::zeroize(&mut old_wits);

    let has_balance_changed = account.balance != updated_account.balance;
    let asset_id_offset = if is_asset_id_revealed { 1 } else { 0 };
    // When include_sk=true, t_acc_new has sk at index 0, so indices match the *_GEN_INDEX constants.
    // When include_sk=false, sk is absent from t_acc_new, so all indices shift down by 1.
    let sk_offset = if include_sk { 0 } else { 1 };

    let mut acc_new_wits = BTreeMap::new();
    if has_balance_changed {
        acc_new_wits.insert(
            BALANCE_GEN_INDEX - sk_offset,
            updated_account.balance.into(),
        );
    }

    acc_new_wits.insert(
        CURRENT_RHO_GEN_INDEX - sk_offset - asset_id_offset,
        updated_account.current_rho,
    );
    acc_new_wits.insert(
        CURRENT_RANDOMNESS_GEN_INDEX - sk_offset - asset_id_offset,
        updated_account.current_randomness,
    );

    if !include_sk {
        let b_blinding_idx = NUM_GENERATORS - 2 - asset_id_offset; // -2 since both sk and sk_enc  absent
        acc_new_wits.insert(b_blinding_idx, host_new_b_blinding_witness.unwrap());
    }

    let resp_acc_new = t_acc_new.partial_response(acc_new_wits, prover_challenge)?;

    Ok((resp_acc_old, resp_acc_new))
}

/// Generate nullifier and BP Schnorr responses (Sigma protocol step 3).
///
/// When `include_sk` is true (solo mode), the BP response includes positions:
///   0 = comm_bp_blinding, 8 = sk_enc_inv.
pub(crate) fn generate_null_bp_responses<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0>>(
    comm_bp_blinding: F0,
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_bp: &SchnorrCommitment<Affine<G0>>,
    sk_enc: Option<F0>, // Only when prover knows sk_enc (solo mode)
    prover_challenge: &F0,
) -> Result<(
    PartialPokDiscreteLog<Affine<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
)> {
    let resp_null = t_null.gen_partial_proof();

    let mut wits = BTreeMap::new();
    wits.insert(0, comm_bp_blinding);
    if let Some(sk_enc) = sk_enc {
        let sk_enc_inv = sk_enc.inverse().ok_or(Error::InvertingZero)?;
        wits.insert(8, sk_enc_inv);
    }
    let resp_bp = t_bp.partial_response(wits, prover_challenge)?;

    Ok((resp_null, resp_bp))
}

/// Generate responses (Sigma protocol step 3) for common state change excluding leg-link.
/// Returns (resp_leaf, resp_acc_new, resp_null, resp_bp).
pub(crate) fn generate_sigma_responses_without_leg_link<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    sk_aff: G0::ScalarField,
    sk_enc: G0::ScalarField,
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    leaf_rerandomization: F0,
    comm_bp_blinding: F0,
    t_acc_old: &SchnorrCommitment<Affine<G0>>,
    t_acc_new: &SchnorrCommitment<Affine<G0>>,
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_bp_randomness_relations: &SchnorrCommitment<Affine<G0>>,
    is_asset_id_revealed: bool,
    prover_challenge: &F0,
) -> Result<(
    SchnorrResponse<Affine<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
    PartialPokDiscreteLog<Affine<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
)> {
    let (resp_acc_old, resp_acc_new) = generate_account_commitment_responses(
        &account,
        &updated_account,
        t_acc_old,
        t_acc_new,
        is_asset_id_revealed,
        true, // include_sk
        Some(sk_aff),
        Some(sk_enc),
        Some(leaf_rerandomization),
        None,
        None,
        prover_challenge,
    )?;

    let (resp_null, resp_bp) = generate_null_bp_responses(
        comm_bp_blinding,
        t_null,
        t_bp_randomness_relations,
        Some(sk_enc),
        prover_challenge,
    )?;

    Ok((resp_acc_old, resp_acc_new, resp_null, resp_bp))
}

/// Generate leg-link responses (solo only).
pub(crate) fn generate_sigma_responses_for_leg_link<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    t_leg_link: Vec<LegAccountLinkProtocol<G0>>,
) -> Vec<LegAccountLink<G0>> {
    t_leg_link.into_iter().map(|t| t.gen_proof()).collect()
}

/// Generate responses (Sigma protocol step 3) for state change excluding changes related to amount and balances.
/// Calls [`generate_sigma_responses_without_leg_link`] and [`generate_sigma_responses_for_leg_link`].
pub(crate) fn generate_sigma_responses_for_common_state_change<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    sk_aff: G0::ScalarField,
    sk_enc: G0::ScalarField,
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    leaf_rerandomization: F0,
    comm_bp_blinding: F0,
    t_acc_old: &SchnorrCommitment<Affine<G0>>,
    t_acc_new: &SchnorrCommitment<Affine<G0>>,
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_leg_link: Vec<LegAccountLinkProtocol<G0>>,
    t_bp_randomness_relations: &SchnorrCommitment<Affine<G0>>,
    is_asset_id_revealed: bool,
    prover_challenge: &F0,
) -> Result<(
    SchnorrResponse<Affine<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
    PartialPokDiscreteLog<Affine<G0>>,
    Vec<LegAccountLink<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
)> {
    let (resp_leaf, resp_acc_new, resp_null, resp_bp) = generate_sigma_responses_without_leg_link(
        sk_aff,
        sk_enc,
        account,
        updated_account,
        leaf_rerandomization,
        comm_bp_blinding,
        t_acc_old,
        t_acc_new,
        t_null,
        t_bp_randomness_relations,
        is_asset_id_revealed,
        prover_challenge,
    )?;

    let resp_leg_link = generate_sigma_responses_for_leg_link(t_leg_link);

    Ok((resp_leaf, resp_acc_new, resp_null, resp_leg_link, resp_bp))
}

/// Enforce BP constraints and write challenge contributions for account/BP/null T-values to verifier
/// transcript. Does NOT include leg-link challenge contributions.
pub(crate) fn enforce_constraints_and_take_challenge_contrib_without_leg_link<
    G0: SWCurveConfig + Copy,
>(
    nullifier: &Affine<G0>,
    comm_bp_randomness_relations: Affine<G0>,
    t_acc_old: &Affine<G0>,
    t_acc_new: &Affine<G0>,
    t_randomness_relations: &Affine<G0>,
    resp_null: &PartialPokDiscreteLog<Affine<G0>>,
    verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
) -> Result<()> {
    // Always commit sk_enc and sk_enc_inv to BP (8 values: 6 for rho/rand + 2 for sk_enc/sk_enc_inv)
    let mut vars = verifier.commit_vec(8, comm_bp_randomness_relations);
    // Always enforce the sk_enc * sk_enc_inv = 1 constraint
    enforce_constraints_for_sk_enc_relation(verifier, &mut vars);
    enforce_constraints_for_randomness_relations(verifier, &mut vars);

    let mut transcript = verifier.transcript();

    t_acc_old.serialize_compressed(&mut transcript)?;
    t_acc_new.serialize_compressed(&mut transcript)?;
    t_randomness_relations.serialize_compressed(&mut transcript)?;

    resp_null.challenge_contribution(
        &account_comm_key.current_rho_gen(),
        nullifier,
        &mut transcript,
    )?;

    Ok(())
}

/// Add leg-link verifier challenge contributions to the transcript.
pub(crate) fn add_leg_link_verifier_challenge_contributions<G0: SWCurveConfig + Copy>(
    legs: &[(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )],
    asset_id: Option<AssetId>,
    resp_leg_link: &[LegAccountLink<G0>],
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    enc_gen: Affine<G0>,
    transcript: &mut MerlinTranscript,
) -> Result<()> {
    let enc_key_gen = account_comm_key.sk_enc_gen();
    let is_asset_id_revealed = asset_id.is_some();
    let h_at = asset_id.map(|a| enc_gen * G0::ScalarField::from(a));

    for (i, (core, party_eph_pk)) in legs.iter().enumerate() {
        let is_sender = party_eph_pk.is_sender();
        let eph_pk_participant = party_eph_pk.eph_pk_participant();
        let ct_participant = core.ct_participant(is_sender);

        let resp_participant = resp_leg_link[i].resp_participant();
        resp_participant.challenge_contribution(
            &eph_pk_participant,
            &enc_key_gen,
            &ct_participant,
            &mut *transcript,
        )?;

        if is_asset_id_revealed {
            if core.is_asset_id_revealed() {
                // Asset id revealed in this leg — no extra asset-id ciphertext proof
            } else {
                let eph_pk_base = party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Expected eph_pk_asset_id for leg {i} (asset-id hidden in this leg)"
                    ))
                })?;
                let ct = core.asset_id_ciphertext().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Expected asset_id_ciphertext for leg {i} (asset-id hidden in this leg)"
                    ))
                })?;
                let h_at = h_at.ok_or_else(|| {
                    Error::ProofVerificationError(
                        "asset_id was revealed in at least one leg but no asset_id was provided"
                            .to_string(),
                    )
                })?;
                let y = ct.into_group() - h_at;
                let resp = resp_leg_link[i].resp_asset_id_dl().ok_or_else(|| Error::ProofVerificationError(
                    format!("Asset id is not revealed in leg {i} but expected resp_asset_id_dl for leg-link")
                ))?;
                resp.challenge_contribution(&eph_pk_base, &y.into_affine(), &mut *transcript)?;
            }
        } else {
            let eph_pk_base = party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Expected eph_pk_asset_id for leg {i} (asset-id hidden in all legs)"
                ))
            })?;
            let resp = resp_leg_link[i].resp_asset_id_pc().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in leg {i} but expected resp_asset_id_pc for leg-link"
                ))
            })?;
            resp.challenge_contribution(
                &eph_pk_base,
                &enc_gen,
                &core.asset_id_ciphertext().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Expected asset_id_ciphertext for leg {i} (asset-id hidden in all legs)"
                    ))
                })?,
                &mut *transcript,
            )?;
        }
    }

    Ok(())
}

/// Enforce constraints, take challenge contributions for all T-values including leg-link.
/// Calls [`enforce_constraints_and_take_challenge_contrib_without_leg_link`] and
/// [`add_leg_link_verifier_challenge_contributions`].
pub(crate) fn enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change<
    G0: SWCurveConfig + Copy,
>(
    legs: Vec<(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )>,
    asset_id: Option<AssetId>,
    nullifier: &Affine<G0>,
    comm_bp_randomness_relations: Affine<G0>,
    t_r_leaf: &Affine<G0>,
    t_acc_new: &Affine<G0>,
    t_randomness_relations: &Affine<G0>,
    resp_null: &PartialPokDiscreteLog<Affine<G0>>,
    resp_leg_link: &[LegAccountLink<G0>],
    verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    enc_gen: Affine<G0>,
) -> Result<()> {
    if legs.len() != resp_leg_link.len() {
        return Err(Error::ProofVerificationError(format!(
            "Mismatched leg vector lengths: legs.len() = {}, resp_leg_link.len() = {}",
            legs.len(),
            resp_leg_link.len()
        )));
    }

    enforce_constraints_and_take_challenge_contrib_without_leg_link(
        nullifier,
        comm_bp_randomness_relations,
        t_r_leaf,
        t_acc_new,
        t_randomness_relations,
        resp_null,
        verifier,
        account_comm_key,
    )?;

    let mut transcript = verifier.transcript();
    add_leg_link_verifier_challenge_contributions(
        &legs,
        asset_id,
        resp_leg_link,
        account_comm_key,
        enc_gen,
        &mut transcript,
    )?;

    Ok(())
}

/// Write the balance BP T-value challenge contribution to the verifier transcript.
/// Does NOT include leg-amount challenge contributions.
pub(crate) fn take_challenge_contrib_of_balance_bp<G0: SWCurveConfig + Copy>(
    t_comm_bp_bal: &Affine<G0>,
    verifier_transcript: &mut MerlinTranscript,
) -> Result<()> {
    t_comm_bp_bal.serialize_compressed(verifier_transcript)?;
    Ok(())
}

/// Add leg-amount verifier challenge contributions to the transcript.
pub(crate) fn add_leg_amount_verifier_challenge_contributions<G0: SWCurveConfig + Copy>(
    ct_amounts: &[AmountCiphertext<Affine<G0>>],
    resp_leg_amount: &[PartialPokPedersenCommitment<Affine<G0>>],
    enc_gen: Affine<G0>,
    verifier_transcript: &mut MerlinTranscript,
) -> Result<()> {
    for (resp_leg_amount, &AmountCiphertext(ct_amount, eph_pk_amount)) in
        resp_leg_amount.iter().zip(ct_amounts.iter())
    {
        resp_leg_amount.challenge_contribution(
            &eph_pk_amount,
            &enc_gen,
            &ct_amount,
            &mut *verifier_transcript,
        )?;
    }
    Ok(())
}

/// Take challenge contributions for balance T-values including leg-amount.
/// Calls [`take_challenge_contrib_of_balance_bp`] and [`add_leg_amount_verifier_challenge_contributions`].
pub(crate) fn take_challenge_contrib_of_sigma_t_values_for_balance_change<
    G0: SWCurveConfig + Copy,
>(
    ct_amounts: &[AmountCiphertext<Affine<G0>>],
    t_comm_bp_bal: &Affine<G0>,
    resp_leg_amount: &[PartialPokPedersenCommitment<Affine<G0>>],
    enc_gen: Affine<G0>,
    mut verifier_transcript: &mut MerlinTranscript,
) -> Result<()> {
    if ct_amounts.len() != resp_leg_amount.len() {
        return Err(Error::ProofVerificationError(format!(
            "Mismatched amount vector lengths: ct_amounts.len() = {}, resp_leg_amount.len() = {}",
            ct_amounts.len(),
            resp_leg_amount.len()
        )));
    }
    take_challenge_contrib_of_balance_bp(t_comm_bp_bal, &mut verifier_transcript)?;
    add_leg_amount_verifier_challenge_contributions(
        ct_amounts,
        resp_leg_amount,
        enc_gen,
        &mut verifier_transcript,
    )?;
    Ok(())
}

/// Verify leg-link proofs for each leg (participant ciphertext + asset-id proofs).
/// `resp_sk_enc_inv_bp` is the response for sk_enc_inv extracted from resp_bp.
/// `resp_sk_enc_leaf` is the response for sk_enc from resp_leaf.
/// `resp_asset_id_leaf` is the response for asset_id from resp_leaf (only when asset_id is hidden).
pub(crate) fn verify_leg_link_for_common_state_change<G0: SWCurveConfig + Copy>(
    legs: &[(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )],
    asset_id: Option<AssetId>,
    resp_leg_link: &[LegAccountLink<G0>],
    resp_sk_enc_inv_bp: &G0::ScalarField,
    resp_sk_enc_leaf: &G0::ScalarField,
    resp_asset_id_leaf: Option<&G0::ScalarField>,
    verifier_challenge: &G0::ScalarField,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    enc_gen: Affine<G0>,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
) -> Result<()> {
    let enc_key_gen = account_comm_key.sk_enc_gen();
    let h_at = asset_id.map(|a| enc_gen * G0::ScalarField::from(a));

    for i in 0..legs.len() {
        let (core, party_eph_pk) = &legs[i];
        let is_sender = party_eph_pk.is_sender();

        let eph_pk_participant = party_eph_pk.eph_pk_participant();
        let ct_participant = core.ct_participant(is_sender);
        let resp_participant = resp_leg_link[i].resp_participant();
        verify_or_rmc_3!(
            rmc,
            resp_participant,
            format!("Participant ciphertext verification failed for leg {i}"),
            ct_participant,
            eph_pk_participant,
            enc_key_gen,
            verifier_challenge,
            resp_sk_enc_inv_bp,
            resp_sk_enc_leaf,
        );

        if asset_id.is_none() {
            let eph_pk_base = party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in any leg but leg {i} is missing eph_pk_asset_id"
                ))
            })?;
            let resp = resp_leg_link[i].resp_asset_id_pc().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in leg {i} but resp_asset_id_pc for leg-link is not provided"
                ))
            })?;
            let ct_asset_id = core.asset_id_ciphertext().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in any leg but leg {i} is missing asset-id ciphertext"
                ))
            })?;
            let resp_asset_id = resp_asset_id_leaf.ok_or_else(|| {
                Error::ProofVerificationError(
                    "resp_asset_id_leaf must be provided when asset_id is hidden".to_string(),
                )
            })?;
            verify_or_rmc_3!(
                rmc,
                resp,
                format!("Asset-id ciphertext verification failed for leg {i}"),
                ct_asset_id,
                eph_pk_base,
                enc_gen,
                verifier_challenge,
                resp_sk_enc_inv_bp,
                resp_asset_id,
            );
        } else {
            if core.is_asset_id_revealed() {
                // Asset id revealed in this leg — no extra proof needed
            } else {
                let eph_pk_base = party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Asset id is not revealed in leg {i} but eph_pk_asset_id is missing"
                    ))
                })?;
                let ct_asset_id = core.asset_id_ciphertext().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Asset id is not revealed in leg {i} but asset-id ciphertext is missing"
                    ))
                })?;
                let h_at = h_at.ok_or_else(|| {
                    Error::ProofVerificationError(
                        "Asset id is expected to be known (h_at) when any leg reveals the asset id"
                            .to_string(),
                    )
                })?;
                let y = ct_asset_id.into_group() - h_at;
                let resp = resp_leg_link[i].resp_asset_id_dl().ok_or_else(|| Error::ProofVerificationError(
                    format!("Asset id is not revealed in leg {i} but resp_asset_id_dl for leg-link is not provided")
                ))?;
                verify_or_rmc_2!(
                    rmc,
                    resp,
                    format!(
                        "Asset-id ciphertext (revealed elsewhere) verification failed for leg {i}"
                    ),
                    y.into_affine(),
                    eph_pk_base,
                    verifier_challenge,
                    resp_sk_enc_inv_bp,
                );
            }
        }
    }

    Ok(())
}

/// Verify leg-amount proofs for balance changes (solo only).
pub(crate) fn verify_leg_amount_for_balance_change<G0: SWCurveConfig + Copy>(
    ct_amounts: &[AmountCiphertext<Affine<G0>>],
    resp_leg_amount: &[PartialPokPedersenCommitment<Affine<G0>>],
    resp_comm_bp_bal: &PartialSchnorrResponse<Affine<G0>>,
    resp_sk_enc_inv: G0::ScalarField,
    verifier_challenge: &G0::ScalarField,
    enc_gen: Affine<G0>,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
) -> Result<()> {
    for i in 0..ct_amounts.len() {
        let AmountCiphertext(ct_amount, eph_pk_amount) = ct_amounts[i];
        let resp_bp_balance_i = resp_comm_bp_bal
            .responses
            .get(&(1 + i))
            .ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Balance-change sigma verification: missing bp balance response for index {} (key {})",
                    i,
                    1 + i
                ))
            })?;
        verify_or_rmc_3!(
            rmc,
            resp_leg_amount[i],
            "Leg amount verification failed",
            ct_amount,
            eph_pk_amount,
            enc_gen,
            verifier_challenge,
            &resp_sk_enc_inv,
            resp_bp_balance_i,
        );
    }
    Ok(())
}

pub(crate) fn verify_sigma_for_common_state_change<G0: SWCurveConfig + Copy>(
    legs: &[(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )],
    has_counter_decreased: Vec<Option<bool>>,
    has_balance_changed: bool,
    nullifier: &Affine<G0>,
    re_randomized_leaf: &Affine<G0>,
    updated_account_commitment: &Affine<G0>,
    comm_bp: &Affine<G0>,
    t_r_acc_old: &Affine<G0>,
    t_acc_new: &Affine<G0>,
    t_bp: &Affine<G0>,
    resp_acc_old: &SchnorrResponse<Affine<G0>>,
    resp_acc_new: &PartialSchnorrResponse<Affine<G0>>,
    resp_null: &PartialPokDiscreteLog<Affine<G0>>,
    resp_leg_link: &[LegAccountLink<G0>],
    resp_bp: &PartialSchnorrResponse<Affine<G0>>,
    verifier_challenge: &G0::ScalarField,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_gen: Affine<G0>,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
) -> Result<Option<AssetId>> {
    if legs.len() != has_counter_decreased.len() {
        return Err(Error::ProofVerificationError(format!(
            "Mismatched leg vector lengths: legs.len() = {}, has_counter_decreased.len() = {}",
            legs.len(),
            has_counter_decreased.len()
        )));
    }
    if legs.len() != resp_leg_link.len() {
        return Err(Error::ProofVerificationError(format!(
            "Mismatched leg vector lengths: legs.len() = {}, resp_leg_link.len() = {}",
            legs.len(),
            resp_leg_link.len()
        )));
    }

    // Determine asset_id from the legs (None = hidden in all legs)
    let mut asset_id: Option<AssetId> = None;
    for (l, _) in legs {
        if asset_id.is_none() {
            asset_id = l.asset_id();
        } else if l.is_asset_id_revealed() && (asset_id != l.asset_id()) {
            return Err(Error::ProofVerificationError(
                "All legs must have the same asset id".to_string(),
            ));
        }
    }

    let is_asset_id_revealed = asset_id.is_some();
    // +1 for re-randomization (curve tree)
    let required_resp_acc_old_len = if !is_asset_id_revealed {
        SK_ENC_INV_GEN_INDEX + 1
    } else {
        SK_ENC_INV_GEN_INDEX
    };
    if resp_acc_old.0.len() < required_resp_acc_old_len {
        return Err(Error::ProofVerificationError(format!(
            "Common state-change sigma verification: resp_leaf response length is {} but expected at least {}",
            resp_acc_old.0.len(),
            required_resp_acc_old_len
        )));
    }

    let gens_acc_old = if !is_asset_id_revealed {
        account_comm_key
            .as_gens_with_blinding(pc_gens.B_blinding)
            .to_vec()
    } else {
        account_comm_key
            .as_gens_with_blinding_and_asset_id_revealed(pc_gens.B_blinding)
            .to_vec()
    };

    let y = match asset_id {
        None => *re_randomized_leaf,
        Some(asset_id) => (*re_randomized_leaf
            - (account_comm_key.asset_id_gen() * G0::ScalarField::from(asset_id)))
        .into_affine(),
    };
    verify_schnorr_resp_or_rmc!(
        rmc,
        resp_acc_old,
        gens_acc_old,
        y,
        *t_r_acc_old,
        verifier_challenge,
    );

    let mut y = updated_account_commitment.into_group();
    let counter_gen = account_comm_key.counter_gen().into_group();
    for has_counter_decreased in has_counter_decreased.iter() {
        if let Some(has_counter_decreased) = has_counter_decreased {
            if *has_counter_decreased {
                y += counter_gen;
            } else {
                y -= counter_gen;
            }
        }
    }
    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(SK_GEN_INDEX, resp_acc_old.0[SK_GEN_INDEX]);
    // If balance didn't change, then resp_leaf would contain the response for witness `balance`
    // else response is present in `resp_acc_new`
    if !has_balance_changed {
        missing_resps.insert(BALANCE_GEN_INDEX, resp_acc_old.0[BALANCE_GEN_INDEX]);
    }
    missing_resps.insert(COUNTER_GEN_INDEX, resp_acc_old.0[COUNTER_GEN_INDEX]);

    let offset_when_asset_id_revealed = match asset_id {
        Some(asset_id) => {
            // If asset-id is revealed, then its knowledge in new account commitment is not being proven and new account commitment has to be reduced accordingly
            y -= account_comm_key.asset_id_gen() * G0::ScalarField::from(asset_id);
            1
        }
        None => {
            missing_resps.insert(ASSET_ID_GEN_INDEX, resp_acc_old.0[ASSET_ID_GEN_INDEX]);
            0
        }
    };
    // Since response for asset id is not present when revealed, adjust indices of remaining responses accordingly
    missing_resps.insert(
        RHO_GEN_INDEX - offset_when_asset_id_revealed,
        resp_acc_old.0[RHO_GEN_INDEX - offset_when_asset_id_revealed],
    );
    missing_resps.insert(
        RANDOMNESS_GEN_INDEX - offset_when_asset_id_revealed,
        resp_acc_old.0[RANDOMNESS_GEN_INDEX - offset_when_asset_id_revealed],
    );
    missing_resps.insert(
        ID_GEN_INDEX - offset_when_asset_id_revealed,
        resp_acc_old.0[ID_GEN_INDEX - offset_when_asset_id_revealed],
    );
    missing_resps.insert(
        SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed,
        resp_acc_old.0[SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed],
    );

    let gens_acc_new = if asset_id.is_none() {
        account_comm_key.as_gens().to_vec()
    } else {
        account_comm_key.as_gens_with_asset_id_revealed().to_vec()
    };

    verify_partial_schnorr_resp_or_rmc!(
        rmc,
        resp_acc_new,
        gens_acc_new,
        y.into_affine(),
        *t_acc_new,
        verifier_challenge,
        missing_resps,
    );

    verify_or_rmc_2!(
        rmc,
        resp_null,
        "Nullifier verification failed",
        *nullifier,
        account_comm_key.current_rho_gen(),
        verifier_challenge,
        &resp_acc_old.0[CURRENT_RHO_GEN_INDEX - offset_when_asset_id_revealed],
    );

    // The response for sk_enc_inv (position 8 in BP) is always in resp_bp.responses
    let resp_sk_enc_inv_bp = resp_bp
        .responses
        .get(&8)
        .ok_or_else(|| {
            Error::ProofVerificationError(
                "Common state-change sigma verification: missing response for sk_enc_inv in resp_bp (index 8)"
                    .to_string(),
            )
        })?;

    verify_leg_link_for_common_state_change(
        legs,
        asset_id,
        resp_leg_link,
        resp_sk_enc_inv_bp,
        &resp_acc_old.0[SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed],
        asset_id
            .is_none()
            .then(|| &resp_acc_old.0[ASSET_ID_GEN_INDEX]),
        verifier_challenge,
        account_comm_key,
        enc_gen,
        rmc.as_deref_mut(),
    )?;

    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(1, resp_acc_old.0[4 - offset_when_asset_id_revealed]);
    missing_resps.insert(2, resp_acc_old.0[5 - offset_when_asset_id_revealed]);
    let resp_acc_new_cur_rho = resp_acc_new
        .responses
        .get(&(5 - offset_when_asset_id_revealed))
        .ok_or_else(|| {
            Error::ProofVerificationError(
                "Common state-change sigma verification: missing response for new account current_rho"
                    .to_string(),
            )
        })?;
    missing_resps.insert(3, *resp_acc_new_cur_rho);
    missing_resps.insert(4, resp_acc_old.0[6 - offset_when_asset_id_revealed]);
    missing_resps.insert(5, resp_acc_old.0[7 - offset_when_asset_id_revealed]);
    let resp_acc_new_cur_rand = resp_acc_new
        .responses
        .get(&(7 - offset_when_asset_id_revealed))
        .ok_or_else(|| {
            Error::ProofVerificationError(
                "Common state-change sigma verification: missing response for new account current_randomness"
                    .to_string(),
            )
        })?;
    missing_resps.insert(6, *resp_acc_new_cur_rand);
    // Position 7: sk_enc (shared with resp_leaf at SK_ENC_INV_GEN_INDEX, adjusted for asset_id offset)
    missing_resps.insert(
        7,
        resp_acc_old.0[SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed],
    );
    // Position 8: sk_enc_inv — provided by resp_bp (not in missing_resps)

    // Always use bp_gens for randomness and sk_enc relation (sk_enc and sk_enc_inv always committed)
    let bp_ver_gens = bp_gens_vec_for_randomness_and_sk_enc_relations(pc_gens, bp_gens).to_vec();
    verify_partial_schnorr_resp_or_rmc!(
        rmc,
        resp_bp,
        bp_ver_gens,
        *comm_bp,
        *t_bp,
        verifier_challenge,
        missing_resps,
    );

    Ok(asset_id)
}

pub(crate) fn verify_sigma_for_balance_change<G0: SWCurveConfig + Copy>(
    ct_amounts: &[AmountCiphertext<Affine<G0>>],
    resp_leg_amount: &[PartialPokPedersenCommitment<Affine<G0>>],
    comm_bp_bal: &Affine<G0>,
    t_comm_bp_bal: &Affine<G0>,
    resp_comm_bp_bal: &PartialSchnorrResponse<Affine<G0>>,
    verifier_challenge: &G0::ScalarField,
    resp_old_bal: G0::ScalarField,
    resp_new_bal: G0::ScalarField,
    resp_sk_enc_inv: G0::ScalarField,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_gen: Affine<G0>,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
) -> Result<()> {
    if ct_amounts.len() != resp_leg_amount.len() {
        return Err(Error::ProofVerificationError(format!(
            "Balance-change sigma verification: ct_amounts.len() ({}) != resp_leg_amount.len() ({})",
            ct_amounts.len(),
            resp_leg_amount.len()
        )));
    }

    let mut gens = bp_gens_for_vec_commitment(2 + resp_leg_amount.len() as u32, bp_gens);
    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(1 + resp_leg_amount.len(), resp_old_bal);
    missing_resps.insert(1 + resp_leg_amount.len() + 1, resp_new_bal);

    let mut bp_bal_gens = Vec::with_capacity(3 + resp_leg_amount.len());
    bp_bal_gens.push(pc_gens.B_blinding);
    for _ in 0..2 + resp_leg_amount.len() {
        bp_bal_gens.push(gens.next().unwrap());
    }

    verify_partial_schnorr_resp_or_rmc!(
        rmc,
        resp_comm_bp_bal,
        bp_bal_gens,
        *comm_bp_bal,
        *t_comm_bp_bal,
        verifier_challenge,
        missing_resps,
    );

    verify_leg_amount_for_balance_change(
        ct_amounts,
        resp_leg_amount,
        resp_comm_bp_bal,
        resp_sk_enc_inv,
        verifier_challenge,
        enc_gen,
        rmc.as_deref_mut(),
    )?;

    Ok(())
}

/// Enforces the constraints for relations between initial rho, current rho, old and new randomness
/// `committed_variables` are variables for committed values `[rho, rho^i, rho^{i+1}, s, s^j, s^{j+1}]`
pub(crate) fn enforce_constraints_for_randomness_relations<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    committed_variables: &mut Vec<Variable<F>>,
) {
    let var_s_i_plus_1 = committed_variables.pop().unwrap();
    let var_s_i = committed_variables.pop().unwrap();
    let var_s = committed_variables.pop().unwrap();
    let var_rho_i_plus_1 = committed_variables.pop().unwrap();
    let var_rho_i = committed_variables.pop().unwrap();
    let var_rho = committed_variables.pop().unwrap();

    let (_, _, var_rho_i_plus_1_) = cs.multiply(var_rho.into(), var_rho_i.into());
    let (_, _, var_s_i_plus_1_) = cs.multiply(var_s.into(), var_s_i.into());
    cs.constrain(var_rho_i_plus_1 - var_rho_i_plus_1_);
    cs.constrain(var_s_i_plus_1 - var_s_i_plus_1_);
}

pub(crate) fn enforce_constraints_for_sk_enc_relation<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    committed_variables: &mut Vec<Variable<F>>,
) {
    let sk_enc_inv_var = committed_variables.pop().unwrap();
    let sk_enc_var = committed_variables.pop().unwrap();
    let (_, _, one) = cs.multiply(sk_enc_inv_var.into(), sk_enc_var.into());
    cs.constrain(one - LinearCombination::from(Variable::One(PhantomData)));
}

fn bp_gens_vec_for_randomness_and_sk_enc_relations<G0: SWCurveConfig + Copy>(
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
) -> [Affine<G0>; 9] {
    let mut gens = bp_gens_for_vec_commitment(8, bp_gens);
    [
        pc_gens.B_blinding,
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
    ]
}

/// Like [`bp_gens_vec_for_randomness_and_sk_enc_relations`] but for 6-variable BP
/// (rho, current_rho, new_current_rho, randomness, current_randomness, new_current_randomness).
/// No sk_enc / sk_enc_inv. Used by host in the split affirmation flow.
pub(crate) fn bp_gens_vec_for_randomness_relations<G0: SWCurveConfig + Copy>(
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

/// Generators used by Bulletproofs to construct vector commitment, i.e. when `commit_vec` is called. The resulting commitment
/// has the first generator as the blinding generator and then these generators follow.
pub fn bp_gens_for_vec_commitment<G: AffineRepr>(
    size: u32,
    bp_gens: &BulletproofGens<G>,
) -> Copied<impl Iterator<Item = &G>> {
    bp_gens.share(0).G(size).copied()
}

/// Add a slice to transcript by first writing the slice length (as index) and then each element
pub fn add_slice_to_transcript<T: CanonicalSerialize>(
    transcript: &mut MerlinTranscript,
    label: &'static [u8],
    slice: &[T],
) -> Result<()> {
    let l = slice.len() as u32;
    transcript.append(label, &l.to_le_bytes());

    let mut buf = vec![];
    for (i, item) in slice.iter().enumerate() {
        // Write the index and then the item
        buf.extend_from_slice(&(i as u32).to_le_bytes());
        item.serialize_compressed(&mut buf)?;
        transcript.append(label, &buf);
        buf.clear()
    }

    Ok(())
}

/// Prove using SelRerandProofParameters (which contains bp_gens)
pub fn prove_with_rng_using_params<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_prover: Prover<MerlinTranscript, Affine<G0>>,
    odd_prover: Prover<MerlinTranscript, Affine<G1>>,
    tree_params: &SelRerandProofParameters<G0, G1>,
    rng: &mut R,
) -> Result<(R1CSProof<Affine<G0>>, R1CSProof<Affine<G1>>)> {
    let even_bp_gens = tree_params.even_parameters.bp_gens();
    let odd_bp_gens = tree_params.odd_parameters.bp_gens();
    prove_with_rng(even_prover, odd_prover, even_bp_gens, odd_bp_gens, rng)
}

/// Get verification tuples using SelRerandProofParameters
pub fn get_verification_tuples_with_rng_using_params<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
    odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
    even_proof: &R1CSProof<Affine<G0>>,
    odd_proof: &R1CSProof<Affine<G1>>,
    rng: &mut R,
) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
    get_verification_tuples_with_rng(even_verifier, odd_verifier, even_proof, odd_proof, rng)
}

pub fn handle_verification_tuples<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    P: SelRerandParametersRef<G0, G1>,
>(
    even_tuple: VerificationTuple<Affine<G0>>,
    odd_tuple: VerificationTuple<Affine<G1>>,
    tree_params: &P,
    rmc: Option<(
        &mut RandomizedMultChecker<Affine<G0>>,
        &mut RandomizedMultChecker<Affine<G1>>,
    )>,
) -> Result<()> {
    match rmc {
        Some((rmc_0, rmc_1)) => {
            add_verification_tuples_to_rmc(even_tuple, odd_tuple, tree_params, rmc_0, rmc_1)
        }
        None => verify_given_verification_tuples(even_tuple, odd_tuple, tree_params),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::{Affine as PallasA, Fr};
    use ark_std::UniformRand;

    fn prove_verify_balance_change(
        pc_gens: &PedersenGens<PallasA>,
        bp_gens: &BulletproofGens<PallasA>,
        old_balance: u64,
        new_balance: u64,
        amount: u64,
        has_balance_decreased: bool,
    ) -> bool {
        let values = vec![
            Fr::from(amount),
            Fr::from(old_balance),
            Fr::from(new_balance),
        ];

        let prover_transcript = MerlinTranscript::new(b"test");
        let mut prover = Prover::new(pc_gens, prover_transcript);
        let (comm, vars) = prover.commit_vec(&values, Fr::from(200u64), bp_gens);

        if enforce_constraints_for_balance_change(
            &mut prover,
            vars,
            vec![has_balance_decreased],
            Some(new_balance),
        )
        .is_err()
        {
            return false;
        }

        let proof = match prover.prove(&bp_gens) {
            Ok(p) => p,
            Err(_) => return false,
        };

        let verifier_transcript = MerlinTranscript::new(b"test");
        let mut verifier = Verifier::new(verifier_transcript);
        let vars = verifier.commit_vec(3, comm);

        if enforce_constraints_for_balance_change(
            &mut verifier,
            vars,
            vec![has_balance_decreased],
            None,
        )
        .is_err()
        {
            return false;
        }

        verifier.verify(&proof, &pc_gens, &bp_gens).is_ok()
    }

    fn prove_verify_balance_change_multi(
        pc_gens: &PedersenGens<PallasA>,
        bp_gens: &BulletproofGens<PallasA>,
        old_balance: u64,
        new_balance: u64,
        amounts: Vec<u64>,
        has_balance_decreased: Vec<bool>,
    ) -> bool {
        let num_amounts = amounts.len();
        let mut values = Vec::with_capacity(1 + num_amounts + 1);
        for amount in amounts {
            values.push(Fr::from(amount));
        }
        values.push(Fr::from(old_balance));
        values.push(Fr::from(new_balance));

        let prover_transcript = MerlinTranscript::new(b"test");
        let mut prover = Prover::new(pc_gens, prover_transcript);
        let (comm, vars) = prover.commit_vec(&values, Fr::from(200u64), bp_gens);

        if enforce_constraints_for_balance_change(
            &mut prover,
            vars,
            has_balance_decreased.clone(),
            Some(new_balance),
        )
        .is_err()
        {
            return false;
        }

        let proof = match prover.prove(&bp_gens) {
            Ok(p) => p,
            Err(_) => return false,
        };

        let verifier_transcript = MerlinTranscript::new(b"test");
        let mut verifier = Verifier::new(verifier_transcript);
        let vars = verifier.commit_vec(values.len(), comm);

        if enforce_constraints_for_balance_change(&mut verifier, vars, has_balance_decreased, None)
            .is_err()
        {
            return false;
        }

        verifier.verify(&proof, &pc_gens, &bp_gens).is_ok()
    }

    #[test]
    fn test_constraints_for_balance_change() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);

        assert!(prove_verify_balance_change(
            &pc_gens, &bp_gens, 100, 60, 40, true
        ));

        assert!(prove_verify_balance_change(
            &pc_gens, &bp_gens, 50, 100, 50, false
        ));

        assert!(prove_verify_balance_change(
            &pc_gens, &bp_gens, 50, 50, 0, false
        ));
        assert!(prove_verify_balance_change(
            &pc_gens, &bp_gens, 50, 50, 0, true
        ));

        assert!(!prove_verify_balance_change(
            &pc_gens, &bp_gens, 100, 60, 20, true
        ));

        assert!(!prove_verify_balance_change(
            &pc_gens, &bp_gens, 50, 100, 20, false
        ));

        assert!(!prove_verify_balance_change(
            &pc_gens, &bp_gens, 100, 60, 40, false
        ));

        assert!(!prove_verify_balance_change(
            &pc_gens, &bp_gens, 50, 100, 50, true
        ));

        let amount = 5;
        let old_bal = (1 << BALANCE_BITS) - amount;
        let new_bal = 1 << BALANCE_BITS;
        assert!(!prove_verify_balance_change(
            &pc_gens, &bp_gens, old_bal, new_bal, amount, false
        ));

        assert!(prove_verify_balance_change_multi(
            &pc_gens,
            &bp_gens,
            100,
            40,
            vec![30, 30],
            vec![true, true]
        ));

        assert!(prove_verify_balance_change_multi(
            &pc_gens,
            &bp_gens,
            50,
            150,
            vec![40, 60],
            vec![false, false]
        ));

        assert!(prove_verify_balance_change_multi(
            &pc_gens,
            &bp_gens,
            100,
            80,
            vec![30, 10],
            vec![true, false]
        ));

        assert!(prove_verify_balance_change_multi(
            &pc_gens,
            &bp_gens,
            80,
            100,
            vec![30, 10],
            vec![false, true]
        ));

        assert!(prove_verify_balance_change_multi(
            &pc_gens,
            &bp_gens,
            100,
            100,
            vec![30, 30],
            vec![true, false]
        ));

        assert!(!prove_verify_balance_change_multi(
            &pc_gens,
            &bp_gens,
            100,
            40,
            vec![30, 20],
            vec![true, true]
        ));

        assert!(!prove_verify_balance_change_multi(
            &pc_gens,
            &bp_gens,
            100,
            40,
            vec![30, 30],
            vec![false, true]
        ));
    }
    fn prove_verify_randomness_relations(
        pc_gens: &PedersenGens<PallasA>,
        bp_gens: &BulletproofGens<PallasA>,
        rho: Fr,
        rho_i: Fr,
        rho_i_plus_1: Fr,
        s: Fr,
        s_i: Fr,
        s_i_plus_1: Fr,
    ) -> bool {
        let values = vec![rho, rho_i, rho_i_plus_1, s, s_i, s_i_plus_1];

        let prover_transcript = MerlinTranscript::new(b"test");
        let mut prover = Prover::new(pc_gens, prover_transcript);
        let (comm, mut vars) = prover.commit_vec(&values, Fr::from(200), bp_gens);

        enforce_constraints_for_randomness_relations(&mut prover, &mut vars);

        let proof = match prover.prove(&bp_gens) {
            Ok(p) => p,
            Err(_) => return false,
        };

        let verifier_transcript = MerlinTranscript::new(b"test");
        let mut verifier = Verifier::new(verifier_transcript);
        let mut vars = verifier.commit_vec(values.len(), comm);

        enforce_constraints_for_randomness_relations(&mut verifier, &mut vars);

        verifier.verify(&proof, &pc_gens, &bp_gens).is_ok()
    }

    #[test]
    fn test_constraints_for_randomness_relations() {
        let pc_gens = PedersenGens::default();
        let bp_gens = BulletproofGens::new(128, 1);
        let mut rng = rand::thread_rng();

        let rho = Fr::rand(&mut rng);
        let rho_i = Fr::rand(&mut rng);
        let rho_i_plus_1 = rho_i * rho;
        let s = Fr::rand(&mut rng);
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s * s_i;
        assert!(prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s,
            s_i,
            s_i_plus_1
        ));

        let rho = Fr::rand(&mut rng);
        let rho_i = Fr::rand(&mut rng);
        let rho_i_plus_1 = rho_i + Fr::ONE;
        let s = Fr::rand(&mut rng);
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s * s_i;
        assert!(!prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s,
            s_i,
            s_i_plus_1
        ));

        let rho = Fr::rand(&mut rng);
        let rho_i = Fr::rand(&mut rng);
        let rho_i_plus_1 = rho_i * rho;
        let s = Fr::rand(&mut rng);
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s_i + Fr::ONE;
        assert!(!prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s,
            s_i,
            s_i_plus_1
        ));

        let rho = Fr::rand(&mut rng);
        let rho_i = Fr::rand(&mut rng);
        let rho_i_plus_1 = rho_i + Fr::ONE;
        let s = Fr::rand(&mut rng);
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s_i + Fr::ONE;
        assert!(!prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s,
            s_i,
            s_i_plus_1
        ));
    }
}
