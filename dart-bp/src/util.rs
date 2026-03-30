use crate::account::common::{LegAccountLink, LegAccountLinkProtocol};
use crate::account::state::{
    ASSET_ID_GEN_INDEX, AccountCommitmentKeyTrait, AccountState, BALANCE_GEN_INDEX,
    COUNTER_GEN_INDEX, CURRENT_RANDOMNESS_GEN_INDEX, CURRENT_RHO_GEN_INDEX, ID_GEN_INDEX,
    RANDOMNESS_GEN_INDEX, RHO_GEN_INDEX, SK_ENC_INV_GEN_INDEX, SK_GEN_INDEX,
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
    let even_pc_gens = tree_params.even_parameters().pc_gens();
    let odd_pc_gens = tree_params.odd_parameters().pc_gens();
    let even_bp_gens = tree_params.even_parameters().bp_gens();
    let odd_bp_gens = tree_params.odd_parameters().bp_gens();
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
    rmc_0: &RandomizedMultChecker<Affine<G0>>,
    rmc_1: &RandomizedMultChecker<Affine<G1>>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_verify, odd_verify) = rayon::join(|| rmc_0.verify(), || rmc_1.verify());

    #[cfg(not(feature = "parallel"))]
    let (even_verify, odd_verify) = (rmc_0.verify(), rmc_1.verify());

    // Return success only if both verifications pass
    if even_verify && odd_verify {
        Ok(())
    } else {
        Err(Error::ProofVerificationError(
            format!("RandomizedMultChecker verification failed: even_verify={even_verify}, odd_verify={odd_verify}").to_string(),
        ))
    }
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

/// Generate commitment to randomness (Sigma protocol step 1) for state change excluding changes related to amount and balances
pub(crate) fn generate_sigma_t_values_for_common_state_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Copy,
>(
    rng: &mut R,
    mut asset_id: AssetId,
    legs: Vec<(
        LegEncryptionCore<Affine<G0>>,
        PartyEphemeralPublicKey<Affine<G0>>,
    )>,
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
    mut old_randomness_blinding: F0,
    mut new_randomness_blinding: F0,
    mut initial_randomness_blinding: F0,
    mut asset_id_blinding: Option<F0>,
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

    let nullifier = old_account.nullifier(account_comm_key);

    let is_asset_id_revealed = asset_id_blinding.is_none();

    let mut sk_enc_blinding = is_asset_id_revealed.then(|| F0::rand(rng));
    let mut sk_enc = is_asset_id_revealed
        .then(|| old_account.sk_enc_inv.inverse().ok_or(Error::InvertingZero))
        .transpose()?;

    let h_at = is_asset_id_revealed.then(|| enc_gen * G0::ScalarField::from(asset_id));

    let comm_bp_blinding = F0::rand(rng);
    let mut wits = vec![
        old_account.rho,
        old_account.current_rho,
        updated_account.current_rho,
        old_account.randomness,
        old_account.current_randomness,
        updated_account.current_randomness,
    ];

    // If asset-id is revealed, then a different relation is used to prove leg was created for this account as a party
    // and that involves using both `sk_enc^{-1}` and `sk_enc` so i need to prove that these are indeed inverses.
    if is_asset_id_revealed {
        wits.push(old_account.sk_enc_inv);
        wits.push(sk_enc.unwrap());
    }

    let (comm_bp_randomness_relations, mut vars) =
        prover.commit_vec(&wits, comm_bp_blinding, bp_gens);

    Zeroize::zeroize(&mut wits);

    if is_asset_id_revealed {
        enforce_constraints_for_sk_enc_relation(prover, &mut vars);
    }

    enforce_constraints_for_randomness_relations(prover, &mut vars);

    // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
    // This could be modified to subtract the nullifier as a public input but it doesn't change the
    // overall proof cost
    let (t_r_leaf, t_acc_new, t_bp_randomness_relations) = match asset_id_blinding {
        Some(asset_id_blinding) => {
            // asset-id is hidden from verifier so its knowledge is proved

            // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
            // This could be modified to subtract the nullifier as a public input but it doesn't change the
            // overall proof cost
            let t_r_leaf = SchnorrCommitment::new(
                &account_comm_key.as_gens_with_blinding(pc_gens.B_blinding),
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
                    sk_enc_inv_blinding,
                    F0::rand(rng),
                ],
            );

            // Schnorr commitment for proving correctness of new account state which will become new leaf
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
                    sk_enc_inv_blinding,
                ],
            );

            // Schnorr commitment for proving correctness of Bulletproof commitment
            let t_bp_randomness_relations = SchnorrCommitment::new(
                &bp_gens_vec_for_randomness_relations(pc_gens, bp_gens),
                vec![
                    F0::rand(rng),
                    initial_rho_blinding,
                    old_rho_blinding,
                    new_rho_blinding,
                    initial_randomness_blinding,
                    old_randomness_blinding,
                    new_randomness_blinding,
                ],
            );

            (t_r_leaf, t_acc_new, t_bp_randomness_relations)
        }
        None => {
            // asset-id is revealed to the verifier

            // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
            // This could be modified to subtract the nullifier as a public input but it doesn't change the
            // overall proof cost
            let t_r_leaf = SchnorrCommitment::new(
                &account_comm_key.as_gens_with_blinding_without_asset_id(pc_gens.B_blinding),
                vec![
                    sk_blinding,
                    old_balance_blinding,
                    old_counter_blinding,
                    initial_rho_blinding,
                    old_rho_blinding,
                    initial_randomness_blinding,
                    old_randomness_blinding,
                    id_blinding,
                    sk_enc_inv_blinding,
                    F0::rand(rng),
                ],
            );

            // Schnorr commitment for proving correctness of new account state which will become new leaf
            let t_acc_new = SchnorrCommitment::new(
                &account_comm_key.as_gens_without_asset_id(),
                vec![
                    sk_blinding,
                    new_balance_blinding,
                    old_counter_blinding,
                    initial_rho_blinding,
                    new_rho_blinding,
                    initial_randomness_blinding,
                    new_randomness_blinding,
                    id_blinding,
                    sk_enc_inv_blinding,
                ],
            );

            // Schnorr commitment for proving correctness of Bulletproof commitment
            let t_bp_randomness_relations = SchnorrCommitment::new(
                &bp_gens_vec_for_randomness_and_sk_enc_relations(pc_gens, bp_gens),
                vec![
                    F0::rand(rng),
                    initial_rho_blinding,
                    old_rho_blinding,
                    new_rho_blinding,
                    initial_randomness_blinding,
                    old_randomness_blinding,
                    new_randomness_blinding,
                    sk_enc_inv_blinding,
                    sk_enc_blinding.unwrap(),
                ],
            );

            (t_r_leaf, t_acc_new, t_bp_randomness_relations)
        }
    };

    let null_gen = account_comm_key.current_rho_gen();

    // Schnorr commitment for proving correctness of nullifier
    let t_null = PokDiscreteLogProtocol::init(old_account.current_rho, old_rho_blinding, &null_gen);

    let mut t_leg_link = Vec::with_capacity(legs.len());

    for (core, party_eph_pk) in legs.iter() {
        match asset_id_blinding {
            Some(asset_id_blinding) => {
                // Asset id is not revealed in any leg

                // unwrap is fine as the check is done in outer function
                let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();

                // ct_asset_id = eph_pk_base * sk_enc_inv + enc_gen * asset_id
                // Both witnesses, `sk_enc_inv` and `asset_id`, are shared with resp_leaf
                t_leg_link.push(LegAccountLinkProtocol::AssetIdHidden(
                    PokPedersenCommitmentProtocol::init(
                        old_account.sk_enc_inv,
                        sk_enc_inv_blinding,
                        &eph_pk_base,
                        F0::from(asset_id),
                        asset_id_blinding,
                        &enc_gen,
                    ),
                ));
            }
            None => {
                // Asset id is revealed in atleast one leg

                if !core.is_asset_id_revealed() {
                    // Asset id not revealed in this leg

                    // unwrap is fine as the check is done in outer function
                    let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();

                    // ct_asset_id - enc_gen * asset_id = eph_pk_base * sk_enc_inv
                    // Since asset-id is revealed eventually, only 1 witness `sk_enc_inv` and that is shared with resp_leaf
                    t_leg_link.push(LegAccountLinkProtocol::AssetIdRevealedElsewhere(
                        PokDiscreteLogProtocol::init(
                            old_account.sk_enc_inv,
                            sk_enc_inv_blinding,
                            &eph_pk_base,
                        ),
                    ));
                } else {
                    // Asset id revealed in this leg

                    let eph_pk_base = party_eph_pk.eph_pk_participant();

                    // `ct_s = eph_pk_base * sk_enc_inv + enc_key_gen * sk_enc` or `ct_r = eph_pk_base * sk_enc_inv + enc_key_gen * sk_enc`
                    // Both witnesses, `sk_enc_inv` and `sk_enc`, are shared with resp_leaf and the bulletproof commitment
                    t_leg_link.push(LegAccountLinkProtocol::AssetIdRevealed(
                        PokPedersenCommitmentProtocol::init(
                            old_account.sk_enc_inv,
                            sk_enc_inv_blinding,
                            &eph_pk_base,
                            sk_enc.unwrap(),
                            sk_enc_blinding.unwrap(),
                            &enc_key_gen,
                        ),
                    ));
                }
            }
        }
    }

    Zeroize::zeroize(&mut asset_id);
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
    Zeroize::zeroize(&mut sk_enc_inv_blinding);
    Zeroize::zeroize(&mut sk_enc_blinding);
    Zeroize::zeroize(&mut sk_enc);

    let mut transcript = prover.transcript();

    // Add challenge contribution of each of the above commitments to the transcript
    t_r_leaf.challenge_contribution(&mut transcript)?;
    t_acc_new.challenge_contribution(&mut transcript)?;
    t_bp_randomness_relations.challenge_contribution(&mut transcript)?;

    t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript)?;

    for (i, (core, party_eph_pk)) in legs.into_iter().enumerate() {
        let is_sender = party_eph_pk.is_sender();
        if is_asset_id_revealed {
            if core.is_asset_id_revealed() {
                // Asset id revealed in this leg
                let eph_pk_base = party_eph_pk.eph_pk_participant();
                let y = core.ct_participant(is_sender);
                t_leg_link[i].pc().unwrap().challenge_contribution(
                    &eph_pk_base,
                    &enc_key_gen,
                    &y,
                    &mut transcript,
                )?;
            } else {
                // Asset id not revealed in this leg
                let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();
                let y = core.asset_id_ciphertext().as_ref().unwrap().into_group() - h_at.unwrap();
                t_leg_link[i].dl().unwrap().challenge_contribution(
                    &eph_pk_base,
                    &y.into_affine(),
                    &mut transcript,
                )?;
            }
        } else {
            // Asset id is not revealed in any leg
            let eph_pk_base = party_eph_pk.eph_pk_asset_id().unwrap();
            t_leg_link[i].pc().unwrap().challenge_contribution(
                &eph_pk_base,
                &enc_gen,
                &core.asset_id_ciphertext().unwrap(),
                &mut transcript,
            )?;
        }
    }

    Ok((
        nullifier,
        comm_bp_randomness_relations,
        comm_bp_blinding,
        t_r_leaf,
        t_acc_new,
        t_null,
        t_leg_link,
        t_bp_randomness_relations,
    ))
}

/// Generate commitment to randomness (Sigma protocol step 1) for state change just related to amount and balances
pub(crate) fn generate_sigma_t_values_for_balance_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    mut amount: Vec<Balance>,
    mut ct_amount: Vec<Affine<G0>>,
    mut old_balance_blinding: F0,
    mut new_balance_blinding: F0,
    mut amount_blinding: Vec<F0>,
    mut sk_enc_inv: F0,
    mut sk_enc_inv_blinding: F0,
    mut eph_pk_amount: Vec<Affine<G0>>,
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
    // +2 for old account balance and new account balance
    let mut gens = bp_gens_for_vec_commitment(2 + amount.len() as u32, bp_gens);
    // Schnorr commitment for proving knowledge of amount, old account balance and new account balance in Bulletproof commitment
    let mut bases = Vec::with_capacity(3 + amount.len());
    let mut blindings = Vec::with_capacity(3 + amount.len());
    bases.push(pc_gens.B_blinding);
    blindings.push(F0::rand(rng));
    for i in 0..amount.len() {
        bases.push(gens.next().unwrap());
        blindings.push(amount_blinding[i]);
    }
    bases.push(gens.next().unwrap());
    bases.push(gens.next().unwrap());
    blindings.push(old_balance_blinding);
    blindings.push(new_balance_blinding);
    let t_comm_bp_bal = SchnorrCommitment::new(&bases, blindings);

    // Schnorr commitment for proving knowledge of amount used in the leg
    let mut t_leg_amount = Vec::with_capacity(eph_pk_amount.len());
    for (i, (amount, amount_blinding)) in
        amount.drain(..).zip(amount_blinding.drain(..)).enumerate()
    {
        t_leg_amount.push(PokPedersenCommitmentProtocol::init(
            sk_enc_inv,
            sk_enc_inv_blinding,
            &eph_pk_amount[i],
            F0::from(amount),
            amount_blinding,
            &enc_gen,
        ));
    }

    Zeroize::zeroize(&mut old_balance_blinding);
    Zeroize::zeroize(&mut new_balance_blinding);
    Zeroize::zeroize(&mut sk_enc_inv);
    Zeroize::zeroize(&mut sk_enc_inv_blinding);

    // Add challenge contribution of each of the above commitments to the transcript
    t_comm_bp_bal.challenge_contribution(&mut prover_transcript)?;

    for (i, (eph_pk_amount, ct_amount)) in
        eph_pk_amount.drain(..).zip(ct_amount.drain(..)).enumerate()
    {
        t_leg_amount[i].challenge_contribution(
            &eph_pk_amount,
            &enc_gen,
            &ct_amount,
            &mut prover_transcript,
        )?;
    }

    Ok((t_comm_bp_bal, t_leg_amount))
}

/// Generate responses (Sigma protocol step 3) for state change excluding changes related to amount and balances
pub(crate) fn generate_sigma_responses_for_common_state_change<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    leaf_rerandomization: F0,
    comm_bp_blinding: F0,
    t_r_leaf: &SchnorrCommitment<Affine<G0>>,
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
    let (resp_leaf, resp_acc_new) = if is_asset_id_revealed {
        let mut wits = [
            account.sk,
            account.balance.into(),
            account.counter.into(),
            account.rho,
            account.current_rho,
            account.randomness,
            account.current_randomness,
            account.id,
            account.sk_enc_inv,
            leaf_rerandomization,
        ];
        let resp_leaf = t_r_leaf.response(&wits, prover_challenge)?;

        Zeroize::zeroize(&mut wits);

        // Response for other witnesses will already be generated in sigma protocols for leaf
        let mut wits = BTreeMap::new();
        if account.balance != updated_account.balance {
            wits.insert(BALANCE_GEN_INDEX, updated_account.balance.into());
        }
        wits.insert(CURRENT_RHO_GEN_INDEX - 1, updated_account.current_rho);
        wits.insert(
            CURRENT_RANDOMNESS_GEN_INDEX - 1,
            updated_account.current_randomness,
        );
        let resp_acc_new = t_acc_new.partial_response(wits, prover_challenge)?;
        (resp_leaf, resp_acc_new)
    } else {
        let mut wits = [
            account.sk,
            account.balance.into(),
            account.counter.into(),
            account.asset_id.into(),
            account.rho,
            account.current_rho,
            account.randomness,
            account.current_randomness,
            account.id,
            account.sk_enc_inv,
            leaf_rerandomization,
        ];
        let resp_leaf = t_r_leaf.response(&wits, prover_challenge)?;

        Zeroize::zeroize(&mut wits);

        // Response for other witnesses will already be generated in sigma protocols for leaf
        let mut wits = BTreeMap::new();
        if account.balance != updated_account.balance {
            wits.insert(BALANCE_GEN_INDEX, updated_account.balance.into());
        }
        wits.insert(CURRENT_RHO_GEN_INDEX, updated_account.current_rho);
        wits.insert(
            CURRENT_RANDOMNESS_GEN_INDEX,
            updated_account.current_randomness,
        );
        let resp_acc_new = t_acc_new.partial_response(wits, prover_challenge)?;
        (resp_leaf, resp_acc_new)
    };

    // Response for other witnesses will already be generated in sigma protocols for leaf and account commitment
    let mut wits = BTreeMap::new();
    wits.insert(0, comm_bp_blinding);
    if is_asset_id_revealed {
        // if asset-id is revealed, BP also proves the inverse relation between sk_enc_inv and sk_enc
        wits.insert(
            SK_ENC_INV_GEN_INDEX - 1,
            account.sk_enc_inv.inverse().ok_or(Error::InvertingZero)?,
        );
    }
    let resp_bp = t_bp_randomness_relations.partial_response(wits, &prover_challenge)?;

    // Response for other witnesses will already be generated in sigma protocol for leaf
    let resp_null = t_null.gen_partial_proof();

    // Responses for both witnesses (sk_enc_inv and asset_id) are already in resp_leaf
    let mut resp_leg_link = Vec::with_capacity(t_leg_link.len());
    for t_leg in t_leg_link.into_iter() {
        resp_leg_link.push(t_leg.gen_partial_proof());
    }

    Ok((resp_leaf, resp_acc_new, resp_null, resp_leg_link, resp_bp))
}

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

    let enc_key_gen = account_comm_key.sk_enc_gen();

    let is_asset_id_revealed = asset_id.is_some();

    // If asset-id is revealed, then enforced inverse relation of sk_enc and sk_enc^{-1} in BP
    let mut vars = verifier.commit_vec(
        6 + if is_asset_id_revealed { 2 } else { 0 },
        comm_bp_randomness_relations,
    );
    if is_asset_id_revealed {
        enforce_constraints_for_sk_enc_relation(verifier, &mut vars);
    }
    enforce_constraints_for_randomness_relations(verifier, &mut vars);

    let mut transcript = verifier.transcript();

    t_r_leaf.serialize_compressed(&mut transcript)?;
    t_acc_new.serialize_compressed(&mut transcript)?;
    t_randomness_relations.serialize_compressed(&mut transcript)?;

    resp_null.challenge_contribution(
        &account_comm_key.current_rho_gen(),
        nullifier,
        &mut transcript,
    )?;

    let h_at = asset_id.map(|a| enc_gen * G0::ScalarField::from(a));

    for (i, (core, party_eph_pk)) in legs.iter().enumerate() {
        let is_sender = party_eph_pk.is_sender();
        if is_asset_id_revealed {
            // Asset id is revealed in atleast one leg
            if core.is_asset_id_revealed() {
                // Asset id revealed in this leg
                let eph_pk_base = party_eph_pk.eph_pk_participant();
                let y = core.ct_participant(is_sender);
                let resp = resp_leg_link[i].pc().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Asset id is revealed in leg {i} but response for leg-link is not provided"
                    ))
                })?;
                resp.challenge_contribution(&eph_pk_base, &enc_key_gen, &y, &mut transcript)?;
            } else {
                // Asset id not revealed in this leg
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
                let resp = resp_leg_link[i].dl().ok_or_else(|| Error::ProofVerificationError(
                    format!("Asset id is not revealed in leg {i} but response for leg-link is not provided")
                ))?;
                resp.challenge_contribution(&eph_pk_base, &y.into_affine(), &mut transcript)?;
            }
        } else {
            // Asset id is not revealed in any leg
            let eph_pk_base = party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Expected eph_pk_asset_id for leg {i} (asset-id hidden in all legs)"
                ))
            })?;
            let resp = resp_leg_link[i].pc().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in leg {i} but response for leg-link is not provided"
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
                &mut transcript,
            )?;
        }
    }

    Ok(())
}

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
    t_comm_bp_bal.serialize_compressed(&mut verifier_transcript)?;
    for (resp_leg_amount, &AmountCiphertext(ct_amount, eph_pk_amount)) in
        resp_leg_amount.iter().zip(ct_amounts.iter())
    {
        resp_leg_amount.challenge_contribution(
            &eph_pk_amount,
            &enc_gen,
            &ct_amount,
            &mut verifier_transcript,
        )?;
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
    t_r_leaf: &Affine<G0>,
    t_acc_new: &Affine<G0>,
    t_bp: &Affine<G0>,
    resp_leaf: &SchnorrResponse<Affine<G0>>,
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

    let required_resp_leaf_len = if asset_id.is_none() {
        SK_ENC_INV_GEN_INDEX + 1
    } else {
        SK_ENC_INV_GEN_INDEX
    };
    if resp_leaf.0.len() < required_resp_leaf_len {
        return Err(Error::ProofVerificationError(format!(
            "Common state-change sigma verification: resp_leaf response length is {} but expected at least {}",
            resp_leaf.0.len(),
            required_resp_leaf_len
        )));
    }

    let enc_key_gen = account_comm_key.sk_enc_gen();

    let h_at = asset_id.map(|a| enc_gen * G0::ScalarField::from(a));

    let leaf_ver_gens = if asset_id.is_none() {
        account_comm_key
            .as_gens_with_blinding(pc_gens.B_blinding)
            .to_vec()
    } else {
        account_comm_key
            .as_gens_with_blinding_without_asset_id(pc_gens.B_blinding)
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
        resp_leaf,
        leaf_ver_gens,
        y,
        *t_r_leaf,
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
    missing_resps.insert(SK_GEN_INDEX, resp_leaf.0[SK_GEN_INDEX]);
    // If balance didn't change, then resp_leaf would contain the response for witness `balance`
    // else response is present in `resp_acc_new`
    if !has_balance_changed {
        missing_resps.insert(BALANCE_GEN_INDEX, resp_leaf.0[BALANCE_GEN_INDEX]);
    }
    missing_resps.insert(COUNTER_GEN_INDEX, resp_leaf.0[COUNTER_GEN_INDEX]);

    let offset_when_asset_id_revealed = if asset_id.is_none() {
        missing_resps.insert(ASSET_ID_GEN_INDEX, resp_leaf.0[ASSET_ID_GEN_INDEX]);
        0
    } else {
        // If asset-id is revealed, then its knowledge in new account commitment is not being proven and new account commitment has to be reduced accordingly
        let asset_id = asset_id.ok_or_else(|| {
            Error::ProofVerificationError(
                "Common state-change sigma verification: expected asset_id to be present"
                    .to_string(),
            )
        })?;
        y -= account_comm_key.asset_id_gen() * G0::ScalarField::from(asset_id);
        1
    };
    // Since response for asset id is not present, adjust indices of remaining responses accordingly
    missing_resps.insert(
        RHO_GEN_INDEX - offset_when_asset_id_revealed,
        resp_leaf.0[RHO_GEN_INDEX - offset_when_asset_id_revealed],
    );
    // randomness (base s) is the same in old and new accounts; its response comes from resp_leaf
    missing_resps.insert(
        RANDOMNESS_GEN_INDEX - offset_when_asset_id_revealed,
        resp_leaf.0[RANDOMNESS_GEN_INDEX - offset_when_asset_id_revealed],
    );
    missing_resps.insert(
        ID_GEN_INDEX - offset_when_asset_id_revealed,
        resp_leaf.0[ID_GEN_INDEX - offset_when_asset_id_revealed],
    );
    missing_resps.insert(
        SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed,
        resp_leaf.0[SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed],
    );

    let acc_ver_gens = if asset_id.is_none() {
        account_comm_key.as_gens().to_vec()
    } else {
        account_comm_key.as_gens_without_asset_id().to_vec()
    };

    verify_partial_schnorr_resp_or_rmc!(
        rmc,
        resp_acc_new,
        acc_ver_gens,
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
        &resp_leaf.0[CURRENT_RHO_GEN_INDEX - offset_when_asset_id_revealed],
    );

    for i in 0..legs.len() {
        let (core, party_eph_pk) = &legs[i];
        let is_sender = party_eph_pk.is_sender();
        if asset_id.is_none() {
            // Asset id is not revealed in any leg

            let eph_pk_base = party_eph_pk.eph_pk_asset_id().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in any leg but leg {i} is missing eph_pk_asset_id"
                ))
            })?;
            let resp = resp_leg_link[i].pc().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in leg {i} but response for leg-link is not provided"
                ))
            })?;
            let ct_asset_id = core.asset_id_ciphertext().ok_or_else(|| {
                Error::ProofVerificationError(format!(
                    "Asset id is not revealed in any leg but leg {i} is missing asset-id ciphertext"
                ))
            })?;
            verify_or_rmc_3!(
                rmc,
                resp,
                format!("Leg link verification failed for leg {i}"),
                ct_asset_id,
                eph_pk_base,
                enc_gen,
                verifier_challenge,
                &resp_leaf.0[SK_ENC_INV_GEN_INDEX], // sk_enc^{-1}
                &resp_leaf.0[ASSET_ID_GEN_INDEX],   // asset-id
            );
        } else {
            // Asset id is revealed in atleast one leg
            if core.is_asset_id_revealed() {
                // Asset id revealed in this leg
                let eph_pk_base = party_eph_pk.eph_pk_participant();
                let y = core.ct_participant(is_sender);
                let resp = resp_leg_link[i].pc().ok_or_else(|| {
                    Error::ProofVerificationError(format!(
                        "Asset id is revealed in leg {i} but response for leg-link is not provided"
                    ))
                })?;
                let resp_sk_enc = resp_bp
                    .responses
                    .get(&(SK_ENC_INV_GEN_INDEX - 1))
                    .ok_or_else(|| {
                        Error::ProofVerificationError(
                            "Asset id is revealed but response for sk_enc is missing from resp_bp"
                                .to_string(),
                        )
                    })?;
                verify_or_rmc_3!(
                    rmc,
                    resp,
                    format!("Leg link verification failed for leg {i}"),
                    y,
                    eph_pk_base,
                    enc_key_gen,
                    verifier_challenge,
                    &resp_leaf.0[SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed], // sk_enc^{-1} offset decreased since asset id is revealed
                    resp_sk_enc,                                                        // sk_enc
                );
            } else {
                // Asset id not revealed in this leg
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
                let resp = resp_leg_link[i].dl().ok_or_else(|| Error::ProofVerificationError(
                    format!("Asset id is not revealed in leg {i} but response for leg-link is not provided")
                ))?;
                verify_or_rmc_2!(
                    rmc,
                    resp,
                    format!("Leg link verification failed for leg {i}"),
                    y.into_affine(),
                    eph_pk_base,
                    verifier_challenge,
                    &resp_leaf.0[SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed], // sk_enc^{-1} offset decreased since asset id is revealed
                );
            }
        }
    }

    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(1, resp_leaf.0[4 - offset_when_asset_id_revealed]);
    missing_resps.insert(2, resp_leaf.0[5 - offset_when_asset_id_revealed]);
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
    missing_resps.insert(4, resp_leaf.0[6 - offset_when_asset_id_revealed]);
    missing_resps.insert(5, resp_leaf.0[7 - offset_when_asset_id_revealed]);
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

    let bp_ver_gens = if asset_id.is_none() {
        bp_gens_vec_for_randomness_relations(pc_gens, bp_gens).to_vec()
    } else {
        // Add response for sk_enc^{-1}
        missing_resps.insert(
            7,
            resp_leaf.0[SK_ENC_INV_GEN_INDEX - offset_when_asset_id_revealed],
        );
        bp_gens_vec_for_randomness_and_sk_enc_relations(pc_gens, bp_gens).to_vec()
    };
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

fn bp_gens_vec_for_randomness_relations<G0: SWCurveConfig + Copy>(
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
