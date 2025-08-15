use crate::poseidon_impls::utils::mat_mut_vec_mul;
use ark_ec::AffineRepr;
use ark_ff::Field;
use ark_std::marker::PhantomData;
use bulletproofs::PedersenGens;
use bulletproofs::r1cs::LinearCombination;
use bulletproofs::r1cs::constraint_system::constrain_lc_with_scalar;
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSError, Variable, Verifier};
use dock_crypto_utils::transcript::MerlinTranscript;

pub struct PoseidonParams<F: Field> {
    pub width: usize,
    pub full_rounds: usize,
    pub partial_rounds: usize,
    /// [round][width]
    pub round_constants: Vec<Vec<F>>,
    /// [width][width]
    pub MDS_matrix: Vec<Vec<F>>,
}

impl<F: Field> PoseidonParams<F> {
    pub fn new(width: usize, full_rounds: usize, partial_rounds: usize) -> PoseidonParams<F> {
        let total_rounds = full_rounds + partial_rounds;
        let round_constants = Self::gen_round_constants(width, total_rounds);
        let matrix_2 = Self::gen_MDS_matrix(width);
        PoseidonParams {
            width,
            full_rounds,
            partial_rounds,
            round_constants,
            MDS_matrix: matrix_2,
        }
    }

    pub fn gen_round_constants(width: usize, total_rounds: usize) -> Vec<Vec<F>> {
        let mut test_rng = rand::thread_rng();
        (0..total_rounds)
            .map(|_| (0..width).map(|_| F::rand(&mut test_rng)).collect())
            .collect()
        /*if ROUND_CONSTS.len() < cap {
            panic!("Not enough round constants, need {}, found {}", cap, ROUND_CONSTS.len());
        }
        let mut rc = vec![];
        for i in 0..cap {
            // TODO: Remove unwrap, handle error
            let c = get_scalar_from_hex(ROUND_CONSTS[i]).unwrap();
            rc.push(c);
        }
        rc*/
    }

    // TODO: Write logic to generate correct MDS matrix. Currently loading hardcoded constants.
    pub fn gen_MDS_matrix(width: usize) -> Vec<Vec<F>> {
        let mut test_rng = rand::thread_rng();
        (0..width)
            .map(|_| (0..width).map(|_| F::rand(&mut test_rng)).collect())
            .collect()
        /*if MDS_ENTRIES.len() != width {
            panic!("Incorrect width, only width {} is supported now", width);
        }
        let mut mds: Vec<Vec<F>> = vec![vec![F::zero(); width]; width];
        for i in 0..width {
            if MDS_ENTRIES[i].len() != width {
                panic!("Incorrect width, only width {} is supported now", width);
            }
            for j in 0..width {
                // TODO: Remove unwrap, handle error
                mds[i][j] = get_scalar_from_hex(MDS_ENTRIES[i][j]).unwrap();
            }
        }
        mds*/
    }

    pub fn get_total_rounds(&self) -> usize {
        self.full_rounds + self.partial_rounds
    }
}

#[derive(Clone, Debug)]
pub enum SboxType<F: Field> {
    Cube(PhantomData<F>),
    Quint(PhantomData<F>),
    Heptic(PhantomData<F>),
}

impl<F: Field> SboxType<F> {
    pub fn apply_sbox(&self, elem: F) -> F {
        match self {
            SboxType::Cube(_) => (elem * elem) * elem,
            SboxType::Quint(_) => {
                let e2 = elem * elem;
                let e4 = e2 * e2;
                e4 * elem
            }
            SboxType::Heptic(_) => {
                let e2 = elem * elem;
                let e4 = e2 * e2;
                let e6 = e4 * e2;
                e6 * elem
            }
        }
    }

    pub fn synthesize_sbox<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        input_var: LinearCombination<F>,
        round_const: F,
    ) -> Result<Variable<F>, R1CSError> {
        match self {
            SboxType::Cube(_) => Self::synthesize_cube_sbox(cs, input_var, round_const),
            SboxType::Quint(_) => Self::synthesize_quint_sbox(cs, input_var, round_const),
            SboxType::Heptic(_) => Self::synthesize_heptic_sbox(cs, input_var, round_const),
        }
    }

    /// Allocate variables in circuit and enforce constraints when Sbox as heptic (x^7)
    pub fn synthesize_heptic_sbox<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input_var: LinearCombination<F>,
        round_const: F,
    ) -> Result<Variable<F>, R1CSError> {
        let inp_plus_const: LinearCombination<F> = input_var + round_const;
        let (_, _, sqr) = cs.multiply(inp_plus_const.clone(), inp_plus_const.clone());
        let (_, _, quad) = cs.multiply(sqr.clone().into(), sqr.clone().into());
        let (_, _, six) = cs.multiply(quad.clone().into(), sqr.into());
        let (_, _, heptic) = cs.multiply(six.into(), inp_plus_const);
        Ok(heptic)
    }

    /// Allocate variables in circuit and enforce constraints when Sbox as cube
    pub fn synthesize_cube_sbox<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input_var: LinearCombination<F>,
        round_const: F,
    ) -> Result<Variable<F>, R1CSError> {
        let inp_plus_const: LinearCombination<F> = input_var + round_const;
        let (i, _, sqr) = cs.multiply(inp_plus_const.clone(), inp_plus_const);
        let (_, _, cube) = cs.multiply(sqr.into(), i.into());
        Ok(cube)
    }

    /// Allocate variables in circuit and enforce constraints when Sbox as quint (x^5)
    pub fn synthesize_quint_sbox<CS: ConstraintSystem<F>>(
        cs: &mut CS,
        input_var: LinearCombination<F>,
        round_const: F,
    ) -> Result<Variable<F>, R1CSError> {
        let inp_plus_const: LinearCombination<F> = input_var + round_const;
        let (_, _, sqr) = cs.multiply(inp_plus_const.clone(), inp_plus_const.clone());
        let (_, _, quad) = cs.multiply(sqr.into(), sqr.into());
        let (_, _, quint) = cs.multiply(quad.into(), inp_plus_const);
        Ok(quint)
    }
}

pub fn Poseidon_permutation<F: Field>(
    input: &[F],
    params: &PoseidonParams<F>,
    sbox: &SboxType<F>,
) -> Vec<F> {
    let width = params.width;
    assert_eq!(input.len(), width);

    let full_rounds_beginning = params.full_rounds / 2;
    let partial_rounds = params.partial_rounds;
    let total_rounds = params.full_rounds + params.partial_rounds;

    let mut current_state = input.to_owned();
    let mut current_state_temp = vec![F::zero(); width];

    fn apply_linear_layer<F: Field>(state: &mut [F], temp: &mut [F], mds: &Vec<Vec<F>>) {
        mat_mut_vec_mul(mds, state, temp);
    }

    fn apply_round_constants<F: Field>(state: &mut [F], round_constants: &[F]) {
        for (s, rc) in state.iter_mut().zip(round_constants.iter()) {
            *s += *rc;
        }
    }

    // Unified S-box round
    fn apply_sbox<F: Field>(state: &mut [F], sbox: &SboxType<F>, is_partial: bool) {
        let width = state.len();
        for i in 0..width {
            // apply S-box to only first input only if partial round
            if !is_partial || i == 0 {
                state[i] = sbox.apply_sbox(state[i]);
            }
        }
    }

    // println!("Old poseidon permutation");
    // println!("init: {:?}", current_state);
    // Unified loop for all rounds
    for round in 0..total_rounds {
        apply_round_constants(&mut current_state, &params.round_constants[round]);
        // is_partial true for full_rounds_beginning <= round < full_rounds_beginning + partial_rounds
        let is_partial =
            (round >= full_rounds_beginning) && round < (full_rounds_beginning + partial_rounds);
        apply_sbox(&mut current_state, sbox, is_partial);
        apply_linear_layer(
            &mut current_state,
            &mut current_state_temp,
            &params.MDS_matrix,
        );
        // println!("After round {round}: {:?}", current_state);
    }

    current_state
}

pub fn Poseidon_permutation_constraints<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<LinearCombination<F>>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
) -> Result<Vec<LinearCombination<F>>, R1CSError> {
    let width = params.width;
    assert_eq!(input.len(), width);

    let mut output_vars: Vec<LinearCombination<F>> = input;
    let full_rounds_beginning = params.full_rounds / 2;
    let partial_rounds = params.partial_rounds;
    let total_rounds = params.full_rounds + params.partial_rounds;

    // Helper to add round constants to LinearCombination vector
    fn apply_round_constants<F: Field>(vars: &mut [LinearCombination<F>], round_constants: &[F]) {
        for (v, rc) in vars.iter_mut().zip(round_constants.iter()) {
            *v = v.clone() + LinearCombination::<F>::from(*rc);
        }
    }

    // Unified S-box round helper for constraints
    fn apply_sbox<F: Field, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        output_vars: &mut [LinearCombination<F>],
        sbox_type: &SboxType<F>,
        partial: bool,
    ) -> Vec<LinearCombination<F>> {
        let width = output_vars.len();
        let mut sbox_outputs = vec![LinearCombination::<F>::default(); width];
        for i in 0..width {
            // apply S-box to only first input if partial round
            if !partial || i == 0 {
                sbox_outputs[i] = sbox_type
                    .synthesize_sbox(cs, output_vars[i].clone(), F::zero())
                    .unwrap()
                    .into();
            } else {
                sbox_outputs[i] = output_vars[i].clone();
            }
        }
        sbox_outputs
    }

    fn apply_linear_layer<F: Field>(
        width: usize,
        sbox_outs: &[LinearCombination<F>],
        next_inputs: &mut [LinearCombination<F>],
        MDS_matrix: &Vec<Vec<F>>,
    ) {
        for j in 0..width {
            for i in 0..width {
                next_inputs[i] = next_inputs[i].clone() + sbox_outs[j].clone() * MDS_matrix[i][j];
            }
        }
    }

    // Unified loop for all rounds
    for round in 0..total_rounds {
        apply_round_constants(&mut output_vars, &params.round_constants[round]);
        let is_partial =
            round >= full_rounds_beginning && round < full_rounds_beginning + partial_rounds;
        let sbox_outputs = apply_sbox(cs, &mut output_vars, sbox_type, is_partial);
        let mut next_input_vars = vec![LinearCombination::<F>::default(); width];
        apply_linear_layer(
            width,
            &sbox_outputs,
            &mut next_input_vars,
            &params.MDS_matrix,
        );
        for i in 0..width {
            output_vars[i] = next_input_vars.remove(0).simplify();
        }
    }

    Ok(output_vars)
}

pub fn Poseidon_permutation_gadget<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<Variable<F>>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
    output: &[F],
) -> Result<(), R1CSError> {
    let width = params.width;
    assert_eq!(output.len(), width);

    let input_vars: Vec<LinearCombination<F>> = input.iter().map(|e| (*e).into()).collect();
    let permutation_output =
        Poseidon_permutation_constraints::<F, CS>(cs, input_vars, params, sbox_type)?;

    for i in 0..width {
        constrain_lc_with_scalar::<F, CS>(cs, permutation_output[i].to_owned(), output[i]);
    }

    Ok(())
}

/// 2:1 (2 inputs, 1 output) hash from the permutation by passing the first input as zero, 2 of the next 4 as non-zero, a padding constant and rest zero. Choose one of the outputs.

// Choice is arbitrary
pub const PADDING_CONST: u64 = 101;
pub const ZERO_CONST: u64 = 0;

pub fn Poseidon_hash_2<F: Field>(
    xl: F,
    xr: F,
    params: &PoseidonParams<F>,
    sbox: &SboxType<F>,
) -> F {
    // Only 2 inputs to the permutation are set to the input of this hash function,
    // one is set to the padding constant and rest are 0. Always keep the 1st input as 0

    let input = vec![
        F::from(ZERO_CONST),
        xl,
        xr,
        F::from(PADDING_CONST),
        F::from(ZERO_CONST),
        F::from(ZERO_CONST),
    ];

    // Never take the first output
    Poseidon_permutation(&input, params, sbox)[1]
}

pub fn Poseidon_hash_2_constraints<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    xl: LinearCombination<F>,
    xr: LinearCombination<F>,
    statics: Vec<LinearCombination<F>>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
) -> Result<LinearCombination<F>, R1CSError> {
    let width = params.width;
    // Only 2 inputs to the permutation are set to the input of this hash function.
    assert_eq!(statics.len(), width - 2);

    // Always keep the 1st input as 0
    let mut inputs = vec![statics[0].to_owned()];
    inputs.push(xl);
    inputs.push(xr);

    // statics correspond to committed variables with values as PADDING_CONST and 0s and randomness as 0
    for i in 1..statics.len() {
        inputs.push(statics[i].to_owned());
    }
    let permutation_output =
        Poseidon_permutation_constraints::<F, CS>(cs, inputs, params, sbox_type)?;
    Ok(permutation_output[1].to_owned())
}

pub fn Poseidon_hash_2_gadget<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    xl: Variable<F>,
    xr: Variable<F>,
    statics: Vec<Variable<F>>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
    output: F,
) -> Result<(), R1CSError> {
    let statics: Vec<LinearCombination<F>> = statics.iter().map(|s| (*s).into()).collect();
    let hash =
        Poseidon_hash_2_constraints::<F, CS>(cs, xl.into(), xr.into(), statics, params, sbox_type)?;

    constrain_lc_with_scalar::<F, CS>(cs, hash, output);

    Ok(())
}

/// 2:1 hash, only xl, xr, and a single static F::from(PADDING_CONST) at the end
pub fn Poseidon_hash_2_simple<F: Field>(
    xl: F,
    xr: F,
    params: &PoseidonParams<F>,
    sbox: &SboxType<F>,
) -> F {
    let input = vec![xl, xr, F::from(PADDING_CONST)];
    Poseidon_permutation(&input, params, sbox)[0]
}

pub fn Poseidon_hash_2_constraints_simple<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    xl: LinearCombination<F>,
    xr: LinearCombination<F>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
) -> Result<LinearCombination<F>, R1CSError> {
    let inputs = vec![xl, xr, LinearCombination::<F>::from(F::from(PADDING_CONST))];
    let permutation_output =
        Poseidon_permutation_constraints::<F, CS>(cs, inputs, params, sbox_type)?;
    Ok(permutation_output[0].to_owned())
}

pub fn Poseidon_hash_2_gadget_simple<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    xl: Variable<F>,
    xr: Variable<F>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
    output: F,
) -> Result<(), R1CSError> {
    let hash =
        Poseidon_hash_2_constraints_simple::<F, CS>(cs, xl.into(), xr.into(), params, sbox_type)?;

    constrain_lc_with_scalar::<F, CS>(cs, hash, output);

    Ok(())
}

/// Allocate padding constant and zeroes for Prover
pub fn allocate_statics_for_prover<F: Field, G: AffineRepr<ScalarField = F>>(
    prover: &mut Prover<MerlinTranscript, G>,
    num_statics: usize,
) -> Vec<Variable<F>> {
    let mut statics = vec![];
    let (_, var) = prover.commit(F::from(ZERO_CONST), F::zero());
    statics.push(var);

    // Commitment to PADDING_CONST with blinding as 0
    let (_, var) = prover.commit(F::from(PADDING_CONST), F::zero());
    statics.push(var);

    // Commit to 0 with randomness 0 for the rest of the elements of width
    for _ in 2..num_statics {
        let (_, var) = prover.commit(F::from(ZERO_CONST), F::zero());
        statics.push(var);
    }
    statics
}

/// Allocate padding constant and zeroes for Verifier
pub fn allocate_statics_for_verifier<F: Field, G: AffineRepr<ScalarField = F>>(
    verifier: &mut Verifier<MerlinTranscript, G>,
    num_statics: usize,
    pc_gens: &PedersenGens<G>,
) -> Vec<Variable<F>> {
    let mut statics = vec![];
    // Commitment to PADDING_CONST with blinding as 0
    let pad_comm = pc_gens.commit(F::from(PADDING_CONST), F::zero());

    // Commitment to 0 with blinding as 0
    let zero_comm = pc_gens.commit(F::from(ZERO_CONST), F::zero());

    let v = verifier.commit(zero_comm.clone());
    statics.push(v);

    let v = verifier.commit(pad_comm);
    statics.push(v);
    for _ in 2..num_statics {
        let v = verifier.commit(zero_comm.clone());
        statics.push(v);
    }
    statics
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use bulletproofs::BulletproofGens;
    use rand_core::CryptoRngCore;
    use std::time::Instant;

    type PallasA = ark_pallas::Affine;
    type Fr = ark_pallas::Fr;

    pub fn get_poseidon_params<R: CryptoRngCore>(rng: &mut R, width: usize) -> PoseidonParams<Fr> {
        let full_rounds = 8;
        let partial_rounds = 56;
        PoseidonParams::new(width, full_rounds, partial_rounds)
    }

    pub fn poseidon_perm<R: CryptoRngCore>(
        rng: &mut R,
        sbox_type: &SboxType<Fr>,
        transcript_label: &'static [u8],
    ) {
        let s_params = get_poseidon_params(rng, 6);
        let width = s_params.width;

        let input = (0..width).map(|_| Fr::rand(rng)).collect::<Vec<_>>();
        let expected_output = Poseidon_permutation(&input, &s_params, sbox_type);

        /*println!("Input:\n");
        println!("{:?}", &input);
        println!("Expected output:\n");
        println!("{:?}", &expected_output);*/

        let pc_gens = PedersenGens::<PallasA>::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let (proof, commitment) = {
            let prover_transcript = MerlinTranscript::new(transcript_label);
            let mut prover = Prover::new(&pc_gens, prover_transcript);

            let start = Instant::now();
            let (comm, vars) = prover.commit_vec(&input, Fr::rand(rng), &bp_gens);

            assert!(
                Poseidon_permutation_gadget(
                    &mut prover,
                    vars,
                    &s_params,
                    sbox_type,
                    &expected_output
                )
                .is_ok()
            );

            println!(
                "For Poseidon perm width={width}, {:?}, full rounds {}, partial rounds {}, no of constraints is {}",
                sbox_type, s_params.full_rounds, s_params.partial_rounds, &prover.number_of_constraints()
            );

            let proof = prover.prove(&bp_gens).unwrap();
            println!(
                "Proving time is {:?} and size is {}",
                start.elapsed(),
                proof.compressed_size()
            );
            (proof, comm)
        };

        let verifier_transcript = MerlinTranscript::new(transcript_label);
        let mut verifier = Verifier::new(verifier_transcript);

        let start = Instant::now();
        let vars = verifier.commit_vec(width, commitment);
        assert!(
            Poseidon_permutation_gadget(
                &mut verifier,
                vars,
                &s_params,
                sbox_type,
                &expected_output
            )
            .is_ok()
        );

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        println!("Verification time is {:?}", start.elapsed());
    }

    pub fn poseidon_hash_2<R: CryptoRngCore>(
        rng: &mut R,
        sbox_type: &SboxType<Fr>,
        transcript_label: &'static [u8],
    ) {
        let s_params = get_poseidon_params(rng, 6);
        let total_rounds = s_params.get_total_rounds();

        let xl = Fr::rand(rng);
        let xr = Fr::rand(rng);
        let expected_output = Poseidon_hash_2(xl, xr, &s_params, sbox_type);

        /*println!("Input:\n");
        println!("xl={:?}", &xl);
        println!("xr={:?}", &xr);
        println!("Expected output:\n");
        println!("{:?}", &expected_output);*/

        let pc_gens = PedersenGens::<PallasA>::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let (proof, commitment) = {
            let prover_transcript = MerlinTranscript::new(transcript_label);
            let mut prover = Prover::new(&pc_gens, prover_transcript);

            let start = Instant::now();

            let (comm, mut vars) = prover.commit_vec(&[xl, xr], Fr::rand(rng), &bp_gens);

            let num_statics = 4;
            let static_vars = allocate_statics_for_prover(&mut prover, num_statics);

            assert!(
                Poseidon_hash_2_gadget(
                    &mut prover,
                    vars.remove(0),
                    vars.remove(0),
                    static_vars,
                    &s_params,
                    sbox_type,
                    expected_output
                )
                .is_ok()
            );

            println!(
                "For Poseidon hash 2:1 rounds {}, no of constraints is {}",
                total_rounds,
                &prover.number_of_constraints()
            );

            let proof = prover.prove(&bp_gens).unwrap();

            let end = start.elapsed();

            println!(
                "Proving time is {:?} and size is {}",
                end,
                proof.compressed_size()
            );
            (proof, comm)
        };

        let verifier_transcript = MerlinTranscript::new(transcript_label);
        let mut verifier = Verifier::new(verifier_transcript);

        let start = Instant::now();
        let mut vars = verifier.commit_vec(2, commitment);

        let num_statics = 4;
        let static_vars = allocate_statics_for_verifier(&mut verifier, num_statics, &pc_gens);

        assert!(
            Poseidon_hash_2_gadget(
                &mut verifier,
                vars.remove(0),
                vars.remove(0),
                static_vars,
                &s_params,
                sbox_type,
                expected_output
            )
            .is_ok()
        );

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        let end = start.elapsed();

        println!("Verification time is {:?}", end);
    }

    pub fn poseidon_hash_2_simple<R: CryptoRngCore>(
        rng: &mut R,
        sbox_type: &SboxType<Fr>,
        transcript_label: &'static [u8],
    ) {
        let s_params = get_poseidon_params(rng, 3);
        let total_rounds = s_params.get_total_rounds();

        let xl = Fr::rand(rng);
        let xr = Fr::rand(rng);
        let expected_output = Poseidon_hash_2_simple(xl, xr, &s_params, sbox_type);

        let pc_gens = PedersenGens::<PallasA>::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let (proof, commitment) = {
            let prover_transcript = MerlinTranscript::new(transcript_label);
            let mut prover = Prover::new(&pc_gens, prover_transcript);

            let start = Instant::now();

            let (comm, mut vars) = prover.commit_vec(&[xl, xr], Fr::rand(rng), &bp_gens);

            // let h = Poseidon_hash_2_constraints_simple(
            //     &mut prover,
            //     var_l.into(),
            //     var_r.into(),
            //     &s_params,
            //     sbox_type,
            // ).unwrap();
            // println!("expected {:?}", expected_output);
            // println!("prover h {:?}", prover.eval(&h));

            assert!(
                Poseidon_hash_2_gadget_simple(
                    &mut prover,
                    vars.remove(0),
                    vars.remove(0),
                    &s_params,
                    sbox_type,
                    expected_output
                )
                .is_ok()
            );

            println!(
                "For Poseidon hash 2:1 rounds {}, no of constraints is {}",
                total_rounds,
                &prover.number_of_constraints()
            );

            let proof = prover.prove(&bp_gens).unwrap();

            println!(
                "Proving time is {:?} and size is {}",
                start.elapsed(),
                proof.compressed_size()
            );
            (proof, comm)
        };

        let verifier_transcript = MerlinTranscript::new(transcript_label);
        let mut verifier = Verifier::new(verifier_transcript);

        let start = Instant::now();

        let mut vars = verifier.commit_vec(2, commitment);

        assert!(
            Poseidon_hash_2_gadget_simple(
                &mut verifier,
                vars.remove(0),
                vars.remove(0),
                &s_params,
                sbox_type,
                expected_output
            )
            .is_ok()
        );

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());

        println!("Verification time is {:?}", start.elapsed());
    }

    #[test]
    fn test_poseidon_perm_cube_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_perm(
            &mut rng,
            &SboxType::Cube(PhantomData),
            b"Poseidon_perm_cube",
        );
    }

    #[test]
    fn test_poseidon_hash_2_cube_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_hash_2(
            &mut rng,
            &SboxType::Cube(PhantomData),
            b"Poseidon_hash_2_cube",
        );
    }

    #[test]
    fn test_poseidon_hash_2_simple_cube_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_hash_2_simple(
            &mut rng,
            &SboxType::Cube(PhantomData),
            b"Poseidon_hash_2_cube",
        );
    }

    #[test]
    fn test_poseidon_perm_quint_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_perm(
            &mut rng,
            &SboxType::Quint(PhantomData),
            b"Poseidon_perm_quint",
        );
    }

    #[test]
    fn test_poseidon_hash_2_quint_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_hash_2(
            &mut rng,
            &SboxType::Quint(PhantomData),
            b"Poseidon_hash_2_quint",
        );
    }

    #[test]
    fn test_poseidon_hash_2_simple_quint_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_hash_2_simple(
            &mut rng,
            &SboxType::Quint(PhantomData),
            b"Poseidon_hash_2_quint",
        );
    }

    #[test]
    fn test_poseidon_perm_heptic_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_perm(
            &mut rng,
            &SboxType::Heptic(PhantomData),
            b"Poseidon_perm_heptic",
        );
    }

    #[test]
    fn test_poseidon_hash_2_heptic_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_hash_2(
            &mut rng,
            &SboxType::Heptic(PhantomData),
            b"Poseidon_hash_2_heptic",
        );
    }

    #[test]
    fn test_poseidon_hash_2_simple_heptic_sbox() {
        let mut rng = rand::thread_rng();
        poseidon_hash_2_simple(
            &mut rng,
            &SboxType::Heptic(PhantomData),
            b"Poseidon_hash_2_heptic",
        );
    }
}
