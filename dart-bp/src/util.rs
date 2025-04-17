use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier};
use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand::RngCore;

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
) -> (Prover<'g, MerlinTranscript, Affine<G0>>, Prover<'g, MerlinTranscript, Affine<G1>>, SelectAndRerandomizePath<L, G0, G1>, F0) {
    let even_transcript = MerlinTranscript::new(even_label);
    let mut even_prover: Prover<_, Affine<G0>> =
        Prover::new(&tree_parameters.even_parameters.pc_gens, even_transcript);

    let odd_transcript = MerlinTranscript::new(odd_label);
    let mut odd_prover: Prover<_, Affine<G1>> =
        Prover::new(&tree_parameters.odd_parameters.pc_gens, odd_transcript);

    let (re_randomized_path, rerandomization) = leaf_path
        .select_and_rerandomize_prover_gadget(
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
    mut re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    tree_root: &CurveTree<L, 1, G0, G1>,
    tree_parameters: &SelRerandParameters<G0, G1>,
) -> (Verifier<MerlinTranscript, Affine<G0>>, Verifier<MerlinTranscript, Affine<G1>>) {
    let even_transcript = MerlinTranscript::new(even_label);
    let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
    let odd_transcript = MerlinTranscript::new(odd_label);
    let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

    tree_root.add_root_to_randomized_path(&mut re_randomized_path);

    // Enforce constraints for odd level
    re_randomized_path.odd_verifier_gadget(&mut odd_verifier, &tree_parameters, &tree_root);

    // Enforce constraints for even level
    re_randomized_path.even_verifier_gadget(&mut even_verifier, &tree_parameters, &tree_root);

    (even_verifier, odd_verifier)
}