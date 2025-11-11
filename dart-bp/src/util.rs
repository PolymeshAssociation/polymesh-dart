use crate::account::{AccountCommitmentKeyTrait, AccountState};
use crate::error::*;
use crate::leg::LegEncryption;
use crate::{AssetId, BALANCE_BITS, Balance};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, PrimeField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::string::ToString;
use ark_std::{format, vec, vec::Vec};
#[cfg(feature = "std")]
use bulletproofs::r1cs::batch_verify;
use bulletproofs::r1cs::{
    ConstraintSystem, Prover, R1CSProof, Variable, VerificationTuple, Verifier,
    add_verification_tuple_to_rmc, add_verification_tuples_to_rmc as add_vts_to_rmc,
    batch_verify_with_rng, verify_given_verification_tuple,
};
use bulletproofs::{BulletproofGens, PedersenGens};
use core::iter::Copied;
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::{difference, range_proof};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_chacha::ChaChaRng;
use rand_core::{CryptoRng, RngCore, SeedableRng};
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{
    Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
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
        let mut buf = vec![];
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
    R: RngCore,
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
    tree_parameters: &'g SelRerandParameters<G0, G1>,
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
    R: RngCore,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    rng: &mut R,
    leaf_path: CurveTreeWitnessPath<L, G0, G1>,
    tree_parameters: &'g SelRerandParameters<G0, G1>,
    even_transcript: MerlinTranscript,
    odd_transcript: MerlinTranscript,
) -> (
    Prover<'g, MerlinTranscript, Affine<G0>>,
    Prover<'g, MerlinTranscript, Affine<G1>>,
    SelectAndRerandomizePath<L, G0, G1>,
    F0,
) {
    let mut even_prover = Prover::new(&tree_parameters.even_parameters.pc_gens, even_transcript);
    let mut odd_prover = Prover::new(&tree_parameters.odd_parameters.pc_gens, odd_transcript);

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
    tree_parameters: &SelRerandParameters<G0, G1>,
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
    tree_parameters: &SelRerandParameters<G0, G1>,
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
        &tree_parameters,
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
    amount: Balance,
    has_balance_decreased: bool,
    even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
) -> Result<(F0, Affine<G0>)> {
    // Commit to amount, old and new balance
    let comm_bp_bal_blinding = F0::rand(rng);
    let (comm_bp_bal, vars) = even_prover.commit_vec(
        &[F0::from(amount), F0::from(old_bal), F0::from(new_bal)],
        comm_bp_bal_blinding,
        bp_gens,
    );
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
    has_balance_decreased: bool,
    even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
) -> Result<()> {
    let vars = even_verifier.commit_vec(3, comm_bp_bal);

    enforce_constraints_for_balance_change(even_verifier, vars, has_balance_decreased, None)?;

    Ok(())
}

pub fn enforce_constraints_for_balance_change<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut committed_variables: Vec<Variable<F>>,
    has_balance_decreased: bool,
    new_bal: Option<Balance>,
) -> Result<()> {
    let var_amount = committed_variables.remove(0);
    let var_bal_old = committed_variables.remove(0);
    let var_bal_new = committed_variables.remove(0);
    // TODO: Combined the following 2 gadgets reduce 1 constraint
    if has_balance_decreased {
        // old - new balance is correct
        difference(
            cs,
            var_bal_old.into(),
            var_bal_new.into(),
            var_amount.into(),
        )?;
    } else {
        // new - old balance is correct
        difference(
            cs,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )?;
    }
    // new balance does not overflow
    range_proof(cs, var_bal_new.into(), new_bal, BALANCE_BITS.into())?;
    Ok(())
}

/// Generate responses (Schnorr step 3) for state change just related to amount and balances
pub fn generate_schnorr_responses_for_balance_change<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    amount: Balance,
    comm_bp_bal_blinding: G0::ScalarField,
    t_comm_bp_bal: SchnorrCommitment<Affine<G0>>,
    t_leg_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
    prover_challenge: &F0,
) -> Result<(
    PartialSchnorrResponse<Affine<G0>>,
    Partial1PokPedersenCommitment<Affine<G0>>,
)> {
    let mut wits = BTreeMap::new();
    wits.insert(0, comm_bp_bal_blinding);
    wits.insert(1, F0::from(amount));

    // Response for other witnesses will already be generated in sigma protocols for leaf and account commitment
    let resp_comm_bp_bal = t_comm_bp_bal.partial_response(wits, prover_challenge)?;

    // Response for witness will already be generated in sigma protocol for Bulletproof commitment
    let resp_leg_amount = t_leg_amount.clone().gen_partial1_proof(prover_challenge);
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
    tree_params: &SelRerandParameters<G0, G1>,
) -> Result<(R1CSProof<Affine<G0>>, R1CSProof<Affine<G1>>)> {
    let mut rng = rand::thread_rng();
    prove_with_rng(even_prover, odd_prover, tree_params, &mut rng)
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
    tree_params: &SelRerandParameters<G0, G1>,
    rng: &mut R,
) -> Result<(R1CSProof<Affine<G0>>, R1CSProof<Affine<G1>>)> {
    let (mut rng_even, mut rng_odd) = generate_even_odd_rngs(rng);

    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || even_prover.prove_with_rng(&tree_params.even_parameters.bp_gens, &mut rng_even),
        || odd_prover.prove_with_rng(&tree_params.odd_parameters.bp_gens, &mut rng_odd),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover.prove_with_rng(&tree_params.even_parameters.bp_gens, &mut rng_even),
        odd_prover.prove_with_rng(&tree_params.odd_parameters.bp_gens, &mut rng_odd),
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
    tree_params: &SelRerandParameters<G0, G1>,
) -> Result<()> {
    let mut rng = rand::thread_rng();
    verify_with_rng(
        even_verifier,
        odd_verifier,
        even_proof,
        odd_proof,
        tree_params,
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
    tree_params: &SelRerandParameters<G0, G1>,
    rng: &mut R,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            even_verifier.verify(
                even_proof,
                &tree_params.even_parameters.pc_gens,
                &tree_params.even_parameters.bp_gens,
            )
        },
        || {
            odd_verifier.verify(
                odd_proof,
                &tree_params.odd_parameters.pc_gens,
                &tree_params.odd_parameters.bp_gens,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        even_verifier.verify_with_rng(
            even_proof,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            rng,
        ),
        odd_verifier.verify_with_rng(
            odd_proof,
            &tree_params.odd_parameters.pc_gens,
            &tree_params.odd_parameters.bp_gens,
            rng,
        ),
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

#[allow(unused_variables)]
pub fn verify_given_verification_tuples<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_tuple: VerificationTuple<Affine<G0>>,
    odd_tuple: VerificationTuple<Affine<G1>>,
    tree_params: &SelRerandParameters<G0, G1>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            verify_given_verification_tuple(
                even_tuple,
                &tree_params.even_parameters.pc_gens,
                &tree_params.even_parameters.bp_gens,
            )
        },
        || {
            verify_given_verification_tuple(
                odd_tuple,
                &tree_params.odd_parameters.pc_gens,
                &tree_params.odd_parameters.bp_gens,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        verify_given_verification_tuple(
            even_tuple,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
        ),
        verify_given_verification_tuple(
            odd_tuple,
            &tree_params.odd_parameters.pc_gens,
            &tree_params.odd_parameters.bp_gens,
        ),
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
>(
    even_tuple: VerificationTuple<Affine<G0>>,
    odd_tuple: VerificationTuple<Affine<G1>>,
    tree_params: &SelRerandParameters<G0, G1>,
    rmc_0: &mut RandomizedMultChecker<Affine<G0>>,
    rmc_1: &mut RandomizedMultChecker<Affine<G1>>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            add_verification_tuple_to_rmc(
                even_tuple,
                &tree_params.even_parameters.pc_gens,
                &tree_params.even_parameters.bp_gens,
                rmc_0,
            )
        },
        || {
            add_verification_tuple_to_rmc(
                odd_tuple,
                &tree_params.odd_parameters.pc_gens,
                &tree_params.odd_parameters.bp_gens,
                rmc_1,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        add_verification_tuple_to_rmc(
            even_tuple,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            rmc_0,
        ),
        add_verification_tuple_to_rmc(
            odd_tuple,
            &tree_params.odd_parameters.pc_gens,
            &tree_params.odd_parameters.bp_gens,
            rmc_1,
        ),
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
    tree_params: &SelRerandParameters<G0, G1>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            batch_verify(
                even_tuples,
                &tree_params.even_parameters.pc_gens,
                &tree_params.even_parameters.bp_gens,
            )
        },
        || {
            batch_verify(
                odd_tuples,
                &tree_params.odd_parameters.pc_gens,
                &tree_params.odd_parameters.bp_gens,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        batch_verify(
            even_tuples,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
        ),
        batch_verify(
            odd_tuples,
            &tree_params.odd_parameters.pc_gens,
            &tree_params.odd_parameters.bp_gens,
        ),
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
    tree_params: &SelRerandParameters<G0, G1>,
    rng: &mut R,
) -> Result<()> {
    let (mut rng_even, mut rng_odd) = generate_even_odd_rngs(rng);

    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            batch_verify_with_rng(
                even_tuples,
                &tree_params.even_parameters.pc_gens,
                &tree_params.even_parameters.bp_gens,
                &mut rng_even,
            )
        },
        || {
            batch_verify_with_rng(
                odd_tuples,
                &tree_params.odd_parameters.pc_gens,
                &tree_params.odd_parameters.bp_gens,
                &mut rng_odd,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        batch_verify_with_rng(
            even_tuples,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            &mut rng_even,
        ),
        batch_verify_with_rng(
            odd_tuples,
            &tree_params.odd_parameters.pc_gens,
            &tree_params.odd_parameters.bp_gens,
            &mut rng_odd,
        ),
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
    tree_params: &SelRerandParameters<G0, G1>,
    rmc_0: &mut RandomizedMultChecker<Affine<G0>>,
    rmc_1: &mut RandomizedMultChecker<Affine<G1>>,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            add_vts_to_rmc(
                even_tuples,
                &tree_params.even_parameters.pc_gens,
                &tree_params.even_parameters.bp_gens,
                rmc_0,
            )
        },
        || {
            add_vts_to_rmc(
                odd_tuples,
                &tree_params.odd_parameters.pc_gens,
                &tree_params.odd_parameters.bp_gens,
                rmc_1,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        add_vts_to_rmc(
            even_tuples,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            rmc_0,
        ),
        add_vts_to_rmc(
            odd_tuples,
            &tree_params.odd_parameters.pc_gens,
            &tree_params.odd_parameters.bp_gens,
            rmc_1,
        ),
    );

    even_res?;
    odd_res?;

    Ok(())
}

/// Generate commitment to randomness (Sigma protocol step 1) for state change excluding changes related to amount and balances
pub fn generate_sigma_t_values_for_common_state_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Copy,
>(
    rng: &mut R,
    mut asset_id: AssetId,
    leg_enc: &LegEncryption<Affine<G0>>,
    old_account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    is_sender: bool,
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
    mut asset_id_blinding: F0,
    mut r_pk: F0, // r_1 or r_2 depending on sender or receiver
    mut r_4: F0,
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
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    SchnorrCommitment<Affine<G0>>,
)> {
    let nullifier = old_account.nullifier(account_comm_key);

    let comm_bp_blinding = F0::rand(rng);
    let mut wits = [
        old_account.rho,
        old_account.current_rho,
        updated_account.current_rho,
        old_account.randomness,
        updated_account.randomness,
    ];
    let (comm_bp_randomness_relations, vars) = prover.commit_vec(&wits, comm_bp_blinding, bp_gens);

    Zeroize::zeroize(&mut wits);

    enforce_constraints_for_randomness_relations(prover, vars);

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
            old_randomness_blinding,
            id_blinding,
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
            new_randomness_blinding,
            id_blinding,
        ],
    );

    let pk_gen = account_comm_key.sk_gen();
    let null_gen = account_comm_key.current_rho_gen();

    // Schnorr commitment for proving correctness of nullifier
    let t_null = PokDiscreteLogProtocol::init(old_account.current_rho, old_rho_blinding, &null_gen);

    // Schnorr commitment for proving correctness of asset-id used in leg
    let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
        r_4,
        F0::rand(rng),
        &enc_key_gen,
        F0::from(asset_id),
        asset_id_blinding,
        &enc_gen,
    );

    // Schnorr commitment for proving knowledge of secret key of the corresponding party's public key used in leg
    let t_leg_pk = PokPedersenCommitmentProtocol::init(
        r_pk,
        F0::rand(rng),
        &enc_key_gen,
        old_account.sk,
        sk_blinding,
        &pk_gen,
    );

    // Schnorr commitment for proving correctness of Bulletproof commitment
    let t_bp_randomness_relations = SchnorrCommitment::new(
        &bp_gens_vec_for_randomness_relations(pc_gens, bp_gens),
        vec![
            F0::rand(rng),
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
        ],
    );

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
    Zeroize::zeroize(&mut asset_id_blinding);
    Zeroize::zeroize(&mut r_pk);
    Zeroize::zeroize(&mut r_4);

    let mut transcript = prover.transcript();

    // Add challenge contribution of each of the above commitments to the transcript
    t_r_leaf.challenge_contribution(&mut transcript)?;
    t_acc_new.challenge_contribution(&mut transcript)?;
    t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript)?;
    t_leg_asset_id.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        &leg_enc.ct_asset_id,
        &mut transcript,
    )?;
    t_leg_pk.challenge_contribution(
        &enc_key_gen,
        &pk_gen,
        if is_sender {
            &leg_enc.ct_s
        } else {
            &leg_enc.ct_r
        },
        &mut transcript,
    )?;
    t_bp_randomness_relations.challenge_contribution(&mut transcript)?;
    comm_bp_randomness_relations.serialize_compressed(&mut transcript)?;

    Ok((
        nullifier,
        comm_bp_randomness_relations,
        comm_bp_blinding,
        t_r_leaf,
        t_acc_new,
        t_null,
        t_leg_asset_id,
        t_leg_pk,
        t_bp_randomness_relations,
    ))
}

/// Generate commitment to randomness (Sigma protocol step 1) for state change just related to amount and balances
pub fn generate_sigma_t_values_for_balance_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    mut amount: Balance,
    ct_amount: &Affine<G0>,
    mut old_balance_blinding: F0,
    mut new_balance_blinding: F0,
    mut amount_blinding: F0,
    mut r_3: F0,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
    mut prover_transcript: &mut MerlinTranscript,
) -> Result<(
    SchnorrCommitment<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
)> {
    let mut gens = bp_gens_for_vec_commitment(3, bp_gens);
    // Schnorr commitment for proving knowledge of amount, old account balance and new account balance in Bulletproof commitment
    let t_comm_bp_bal = SchnorrCommitment::new(
        &[
            pc_gens.B_blinding,
            gens.next().unwrap(),
            gens.next().unwrap(),
            gens.next().unwrap(),
        ],
        vec![
            F0::rand(rng),
            amount_blinding,
            old_balance_blinding,
            new_balance_blinding,
        ],
    );

    // Schnorr commitment for proving knowledge of amount used in the leg
    let t_leg_amount = PokPedersenCommitmentProtocol::init(
        r_3,
        F0::rand(rng),
        &enc_key_gen,
        F0::from(amount),
        amount_blinding,
        &enc_gen,
    );

    Zeroize::zeroize(&mut amount);
    Zeroize::zeroize(&mut old_balance_blinding);
    Zeroize::zeroize(&mut new_balance_blinding);
    Zeroize::zeroize(&mut amount_blinding);
    Zeroize::zeroize(&mut r_3);

    // Add challenge contribution of each of the above commitments to the transcript
    t_comm_bp_bal.challenge_contribution(&mut prover_transcript)?;
    t_leg_amount.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        ct_amount,
        &mut prover_transcript,
    )?;
    Ok((t_comm_bp_bal, t_leg_amount))
}

/// Generate responses (Sigma protocol step 3) for state change excluding changes related to amount and balances
pub fn generate_sigma_responses_for_common_state_change<
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
    t_leg_asset_id: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_leg_pk: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_bp_randomness_relations: &SchnorrCommitment<Affine<G0>>,
    prover_challenge: &F0,
) -> Result<(
    SchnorrResponse<Affine<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
    PartialPokDiscreteLog<Affine<G0>>,
    Partial1PokPedersenCommitment<Affine<G0>>,
    Partial1PokPedersenCommitment<Affine<G0>>,
    PartialSchnorrResponse<Affine<G0>>,
)> {
    let mut wits = [
        account.sk,
        account.balance.into(),
        account.counter.into(),
        account.asset_id.into(),
        account.rho,
        account.current_rho,
        account.randomness,
        account.id,
        leaf_rerandomization,
    ];
    let resp_leaf = t_r_leaf.response(&wits, prover_challenge)?;

    Zeroize::zeroize(&mut wits);

    // Response for other witnesses will already be generated in sigma protocol for leaf
    let mut wits = BTreeMap::new();
    if account.balance != updated_account.balance {
        wits.insert(1, updated_account.balance.into());
    }
    wits.insert(5, updated_account.current_rho);
    wits.insert(6, updated_account.randomness);
    let resp_acc_new = t_acc_new.partial_response(wits, prover_challenge)?;

    // Response for other witnesses will already be generated in sigma protocol for leaf
    let resp_null = t_null.gen_partial_proof();
    let resp_leg_asset_id = t_leg_asset_id.clone().gen_partial1_proof(prover_challenge);
    let resp_leg_pk = t_leg_pk.clone().gen_partial1_proof(prover_challenge);

    // Response for other witnesses will already be generated in sigma protocols for leaf and account commitment
    let mut wits = BTreeMap::new();
    wits.insert(0, comm_bp_blinding);
    let resp_bp = t_bp_randomness_relations.partial_response(wits, &prover_challenge)?;
    Ok((
        resp_leaf,
        resp_acc_new,
        resp_null,
        resp_leg_asset_id,
        resp_leg_pk,
        resp_bp,
    ))
}

pub fn enforce_constraints_and_take_challenge_contrib_of_sigma_t_values_for_common_state_change<
    G0: SWCurveConfig + Copy,
>(
    leg_enc: &LegEncryption<Affine<G0>>,
    is_sender: bool,
    nullifier: &Affine<G0>,
    comm_bp_randomness_relations: Affine<G0>,
    t_r_leaf: &Affine<G0>,
    t_acc_new: &Affine<G0>,
    t_randomness_relations: &Affine<G0>,
    resp_null: &PartialPokDiscreteLog<Affine<G0>>,
    resp_leg_asset_id: &Partial1PokPedersenCommitment<Affine<G0>>,
    resp_leg_pk: &Partial1PokPedersenCommitment<Affine<G0>>,
    verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
) -> Result<()> {
    let vars = verifier.commit_vec(5, comm_bp_randomness_relations);
    enforce_constraints_for_randomness_relations(verifier, vars);

    let mut transcript = verifier.transcript();

    t_r_leaf.serialize_compressed(&mut transcript)?;
    t_acc_new.serialize_compressed(&mut transcript)?;
    resp_null.challenge_contribution(
        &account_comm_key.current_rho_gen(),
        nullifier,
        &mut transcript,
    )?;
    resp_leg_asset_id.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        &leg_enc.ct_asset_id,
        &mut transcript,
    )?;
    resp_leg_pk.challenge_contribution(
        &enc_key_gen,
        &account_comm_key.sk_gen(),
        if is_sender {
            &leg_enc.ct_s
        } else {
            &leg_enc.ct_r
        },
        &mut transcript,
    )?;

    t_randomness_relations.serialize_compressed(&mut transcript)?;
    comm_bp_randomness_relations.serialize_compressed(&mut transcript)?;

    Ok(())
}

pub fn take_challenge_contrib_of_sigma_t_values_for_balance_change<G0: SWCurveConfig + Copy>(
    ct_amount: &Affine<G0>,
    t_comm_bp_bal: &Affine<G0>,
    resp_leg_amount: &Partial1PokPedersenCommitment<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
    mut verifier_transcript: &mut MerlinTranscript,
) -> Result<()> {
    t_comm_bp_bal.serialize_compressed(&mut verifier_transcript)?;
    resp_leg_amount.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        ct_amount,
        &mut verifier_transcript,
    )?;
    Ok(())
}

pub fn verify_sigma_for_common_state_change<G0: SWCurveConfig + Copy>(
    leg_enc: &LegEncryption<Affine<G0>>,
    is_sender: bool,
    has_counter_decreased: Option<bool>,
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
    resp_leg_asset_id: &Partial1PokPedersenCommitment<Affine<G0>>,
    resp_leg_pk: &Partial1PokPedersenCommitment<Affine<G0>>,
    resp_bp: &PartialSchnorrResponse<Affine<G0>>,
    verifier_challenge: &G0::ScalarField,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
) -> Result<()> {
    match rmc.as_mut() {
        Some(rmc) => {
            resp_leaf.verify_using_randomized_mult_checker(
                account_comm_key
                    .as_gens_with_blinding(pc_gens.B_blinding)
                    .to_vec(),
                *re_randomized_leaf,
                *t_r_leaf,
                verifier_challenge,
                rmc,
            )?;
        }
        None => {
            resp_leaf.is_valid(
                &account_comm_key.as_gens_with_blinding(pc_gens.B_blinding),
                re_randomized_leaf,
                t_r_leaf,
                verifier_challenge,
            )?;
        }
    }

    let y = if let Some(has_counter_decreased) = has_counter_decreased {
        if has_counter_decreased {
            updated_account_commitment.into_group() + account_comm_key.counter_gen()
        } else {
            updated_account_commitment.into_group() - account_comm_key.counter_gen()
        }
    } else {
        updated_account_commitment.into_group()
    };
    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(0, resp_leaf.0[0]);
    // If balance didn't change, then resp_leaf would contain the response for witness `balance`
    // else response is present in `resp_acc_new`
    if !has_balance_changed {
        missing_resps.insert(1, resp_leaf.0[1]);
    }
    missing_resps.insert(2, resp_leaf.0[2]);
    missing_resps.insert(3, resp_leaf.0[3]);
    missing_resps.insert(4, resp_leaf.0[4]);
    missing_resps.insert(7, resp_leaf.0[7]);

    match rmc.as_mut() {
        Some(rmc) => {
            resp_acc_new.verify_using_randomized_mult_checker(
                account_comm_key.as_gens().to_vec(),
                y.into_affine(),
                *t_acc_new,
                verifier_challenge,
                missing_resps,
                rmc,
            )?;
        }
        None => {
            resp_acc_new.is_valid(
                &account_comm_key.as_gens(),
                &y.into_affine(),
                t_acc_new,
                verifier_challenge,
                missing_resps,
            )?;
        }
    }

    match rmc.as_mut() {
        Some(rmc) => {
            resp_null.verify_using_randomized_mult_checker(
                *nullifier,
                account_comm_key.current_rho_gen(),
                verifier_challenge,
                &resp_leaf.0[5],
                rmc,
            );

            resp_leg_asset_id.verify_using_randomized_mult_checker(
                leg_enc.ct_asset_id,
                enc_key_gen,
                enc_gen,
                verifier_challenge,
                &resp_leaf.0[3],
                rmc,
            );

            resp_leg_pk.verify_using_randomized_mult_checker(
                if is_sender {
                    leg_enc.ct_s
                } else {
                    leg_enc.ct_r
                },
                enc_key_gen,
                account_comm_key.sk_gen(),
                verifier_challenge,
                &resp_leaf.0[0],
                rmc,
            );
        }
        None => {
            if !resp_null.verify(
                nullifier,
                &account_comm_key.current_rho_gen(),
                verifier_challenge,
                &resp_leaf.0[5],
            ) {
                return Err(Error::ProofVerificationError(
                    "Nullifier verification failed".to_string(),
                ));
            }
            if !resp_leg_asset_id.verify(
                &leg_enc.ct_asset_id,
                &enc_key_gen,
                &enc_gen,
                verifier_challenge,
                &resp_leaf.0[3],
            ) {
                return Err(Error::ProofVerificationError(
                    "Leg asset ID verification failed".to_string(),
                ));
            }
            if !resp_leg_pk.verify(
                if is_sender {
                    &leg_enc.ct_s
                } else {
                    &leg_enc.ct_r
                },
                &enc_key_gen,
                &account_comm_key.sk_gen(),
                verifier_challenge,
                &resp_leaf.0[0],
            ) {
                return Err(Error::ProofVerificationError(
                    "Leg public key verification failed".to_string(),
                ));
            }
        }
    }

    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(1, resp_leaf.0[4]);
    missing_resps.insert(2, resp_leaf.0[5]);
    missing_resps.insert(3, resp_acc_new.responses[&5]);
    missing_resps.insert(4, resp_leaf.0[6]);
    missing_resps.insert(5, resp_acc_new.responses[&6]);

    match rmc.as_mut() {
        Some(rmc) => {
            resp_bp.verify_using_randomized_mult_checker(
                bp_gens_vec_for_randomness_relations(pc_gens, bp_gens).to_vec(),
                *comm_bp,
                *t_bp,
                verifier_challenge,
                missing_resps,
                rmc,
            )?;
        }
        None => {
            resp_bp.is_valid(
                &bp_gens_vec_for_randomness_relations(pc_gens, bp_gens),
                comm_bp,
                t_bp,
                verifier_challenge,
                missing_resps,
            )?;
        }
    }

    Ok(())
}

pub fn verify_sigma_for_balance_change<G0: SWCurveConfig + Copy>(
    leg_enc: &LegEncryption<Affine<G0>>,
    resp_leg_amount: &Partial1PokPedersenCommitment<Affine<G0>>,
    comm_bp_bal: &Affine<G0>,
    t_comm_bp_bal: &Affine<G0>,
    resp_comm_bp_bal: &PartialSchnorrResponse<Affine<G0>>,
    verifier_challenge: &G0::ScalarField,
    resp_old_bal: G0::ScalarField,
    resp_new_bal: G0::ScalarField,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
) -> Result<()> {
    let mut gens = bp_gens_for_vec_commitment(3, bp_gens);
    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(2, resp_old_bal);
    missing_resps.insert(3, resp_new_bal);

    let bp_bal_gens = [
        pc_gens.B_blinding,
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
    ];

    match rmc.as_mut() {
        Some(rmc) => {
            resp_comm_bp_bal.verify_using_randomized_mult_checker(
                bp_bal_gens.to_vec(),
                *comm_bp_bal,
                *t_comm_bp_bal,
                verifier_challenge,
                missing_resps.clone(),
                rmc,
            )?;
        }
        None => {
            resp_comm_bp_bal.is_valid(
                &bp_bal_gens,
                comm_bp_bal,
                t_comm_bp_bal,
                verifier_challenge,
                missing_resps,
            )?;
        }
    }

    match rmc.as_mut() {
        Some(rmc) => {
            resp_leg_amount.verify_using_randomized_mult_checker(
                leg_enc.ct_amount,
                enc_key_gen,
                enc_gen,
                verifier_challenge,
                &resp_comm_bp_bal.responses[&1],
                rmc,
            );
        }
        None => {
            if !resp_leg_amount.verify(
                &leg_enc.ct_amount,
                &enc_key_gen,
                &enc_gen,
                verifier_challenge,
                &resp_comm_bp_bal.responses[&1],
            ) {
                return Err(Error::ProofVerificationError(
                    "Leg amount verification failed".to_string(),
                ));
            }
        }
    }

    Ok(())
}

/// Enforces the constraints for relations between initial rho, current rho, old and new randomness
/// `committed_variables` are variables for committed values `[rho, rho^i, rho^{i+1}, s^j, s^{2*j}]`
pub fn enforce_constraints_for_randomness_relations<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut committed_variables: Vec<Variable<F>>,
) {
    let var_rho = committed_variables.remove(0);
    let var_rho_i = committed_variables.remove(0);
    let var_rho_i_plus_1 = committed_variables.remove(0);
    let var_s_i = committed_variables.remove(0);
    let var_s_i_plus_1 = committed_variables.remove(0);
    let (_, _, var_rho_i_plus_1_) = cs.multiply(var_rho.into(), var_rho_i.into());
    let (_, _, var_s_i_plus_1_) = cs.multiply(var_s_i.into(), var_s_i.into());
    cs.constrain(var_rho_i_plus_1 - var_rho_i_plus_1_);
    cs.constrain(var_s_i_plus_1 - var_s_i_plus_1_);
}

fn bp_gens_vec_for_randomness_relations<G0: SWCurveConfig + Copy>(
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
) -> [Affine<G0>; 6] {
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
            has_balance_decreased,
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

        // This should fail due to overflow
        let amount = 5;
        let old_bal = (1 << BALANCE_BITS) - amount;
        let new_bal = 1 << BALANCE_BITS;
        assert!(!prove_verify_balance_change(
            &pc_gens, &bp_gens, old_bal, new_bal, amount, false
        ));
    }
    fn prove_verify_randomness_relations(
        pc_gens: &PedersenGens<PallasA>,
        bp_gens: &BulletproofGens<PallasA>,
        rho: Fr,
        rho_i: Fr,
        rho_i_plus_1: Fr,
        s_i: Fr,
        s_i_plus_1: Fr,
    ) -> bool {
        let values = vec![rho, rho_i, rho_i_plus_1, s_i, s_i_plus_1];

        let prover_transcript = MerlinTranscript::new(b"test");
        let mut prover = Prover::new(pc_gens, prover_transcript);
        let (comm, vars) = prover.commit_vec(&values, Fr::from(200), bp_gens);

        enforce_constraints_for_randomness_relations(&mut prover, vars);

        let proof = match prover.prove(&bp_gens) {
            Ok(p) => p,
            Err(_) => return false,
        };

        let verifier_transcript = MerlinTranscript::new(b"test");
        let mut verifier = Verifier::new(verifier_transcript);
        let vars = verifier.commit_vec(values.len(), comm);

        enforce_constraints_for_randomness_relations(&mut verifier, vars);

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
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s_i * s_i;
        assert!(prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s_i,
            s_i_plus_1
        ));

        let rho = Fr::rand(&mut rng);
        let rho_i = Fr::rand(&mut rng);
        let rho_i_plus_1 = rho_i + Fr::ONE;
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s_i * s_i;
        assert!(!prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s_i,
            s_i_plus_1
        ));

        let rho = Fr::rand(&mut rng);
        let rho_i = Fr::rand(&mut rng);
        let rho_i_plus_1 = rho_i * rho;
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s_i + Fr::ONE;
        assert!(!prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s_i,
            s_i_plus_1
        ));

        let rho = Fr::rand(&mut rng);
        let rho_i = Fr::rand(&mut rng);
        let rho_i_plus_1 = rho_i + Fr::ONE;
        let s_i = Fr::rand(&mut rng);
        let s_i_plus_1 = s_i + Fr::ONE;
        assert!(!prove_verify_randomness_relations(
            &pc_gens,
            &bp_gens,
            rho,
            rho_i,
            rho_i_plus_1,
            s_i,
            s_i_plus_1
        ));
    }
}
