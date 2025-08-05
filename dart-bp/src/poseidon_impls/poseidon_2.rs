// The native implementation is taken from here https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2.rs

use bulletproofs::r1cs::{ConstraintSystem, R1CSError, LinearCombination};
use ark_ff::PrimeField;
use bulletproofs::r1cs::constraint_system::constrain_lc_with_scalar;
use crate::poseidon_impls::utils::{mat_inverse, mat_vec_mul};

#[derive(Clone, Debug)]
pub struct Poseidon2Params<F: PrimeField> {
    pub t: usize, // statesize
    pub d: usize, // sbox degree
    pub rounds_f_beginning: usize,
    pub rounds_p: usize,
    #[allow(dead_code)]
    pub rounds_f_end: usize,
    pub rounds: usize,
    pub mat_internal_diag_m_1: Vec<F>,
    pub _mat_internal: Vec<Vec<F>>,
    pub round_constants: Vec<Vec<F>>,
}

impl<F: PrimeField> Poseidon2Params<F> {
    pub fn new(
        t: usize,
        d: usize,
        rounds_f: usize,
        rounds_p: usize,
        mat_internal_diag_m_1: &[F],
        mat_internal: &[Vec<F>],
        round_constants: &[Vec<F>],
    ) -> Self {
        assert!(d == 3 || d == 5 || d == 7 || d == 11);
        assert_eq!(rounds_f % 2, 0);
        let r = rounds_f / 2;
        let rounds = rounds_f + rounds_p;

        Poseidon2Params {
            t,
            d,
            rounds_f_beginning: r,
            rounds_p,
            rounds_f_end: r,
            rounds,
            mat_internal_diag_m_1: mat_internal_diag_m_1.to_owned(),
            _mat_internal: mat_internal.to_owned(),
            round_constants: round_constants.to_owned(),
        }
    }

    // Unused
    pub fn equivalent_round_constants(
        round_constants: &[Vec<F>],
        mat_internal: &[Vec<F>],
        rounds_f_beginning: usize,
        rounds_p: usize,
    ) -> Vec<Vec<F>> {
        let mut opt = vec![Vec::new(); rounds_p + 1];
        let mat_internal_inv = mat_inverse(mat_internal);

        let p_end = rounds_f_beginning + rounds_p - 1;
        let mut tmp = round_constants[p_end].clone();
        for i in (0..rounds_p - 1).rev() {
            let inv_cip = mat_vec_mul(&mat_internal_inv, &tmp);
            opt[i + 1] = vec![inv_cip[0]];
            tmp = round_constants[rounds_f_beginning + i].clone();
            for i in 1..inv_cip.len() {
                tmp[i] += inv_cip[i];
            }
        }
        opt[0] = tmp;
        opt[rounds_p] = vec![F::zero(); opt[0].len()]; // opt[0].len() = t

        opt
    }
}

#[derive(Clone, Debug)]
pub struct Poseidon2<F: PrimeField> {
    pub params: Poseidon2Params<F>,
}

impl<F: PrimeField> Poseidon2<F> {
    pub fn new(params: Poseidon2Params<F>) -> Self {
        Poseidon2 {
            params,
        }
    }

    pub fn get_t(&self) -> usize {
        self.params.t
    }

    pub fn permutation(&self, input: &[F]) -> Vec<F> {
        let t = self.params.t;
        assert_eq!(input.len(), t);

        let mut current_state = input.to_owned();

        // Linear layer at beginning
        self.matmul_external(&mut current_state);

        for r in 0..self.params.rounds_f_beginning {
            current_state = self.add_rc(&current_state, &self.params.round_constants[r]);
            current_state = self.sbox(&current_state);
            self.matmul_external(&mut current_state);
        }

        let p_end = self.params.rounds_f_beginning + self.params.rounds_p;
        for r in self.params.rounds_f_beginning..p_end {
            current_state[0].add_assign(&self.params.round_constants[r][0]);
            current_state[0] = self.sbox_p(&current_state[0]);
            // self.matmul_internal(&mut current_state, &self.params.mat_internal_diag_m_1);
            self.matmul_internal(&mut current_state);
        }
        
        for r in p_end..self.params.rounds {
            current_state = self.add_rc(&current_state, &self.params.round_constants[r]);
            current_state = self.sbox(&current_state);
            self.matmul_external(&mut current_state);
        }
        current_state
    }

    fn sbox(&self, input: &[F]) -> Vec<F> {
        input.iter().map(|el| self.sbox_p(el)).collect()
    }

    fn sbox_p(&self, input: &F) -> F {
        let mut input2 = *input;
        input2.square_in_place();

        match self.params.d {
            3 => {
                let mut out = input2;
                out.mul_assign(input);
                out
            }
            5 => {
                let mut out = input2;
                out.square_in_place();
                out.mul_assign(input);
                out
            }
            7 => {
                let mut out = input2;
                out.square_in_place();
                out.mul_assign(&input2);
                out.mul_assign(input);
                out
            }
            _ => {
                panic!()
            }
        }
    }

    fn matmul_m4(&self, input: &mut[F]) {
        let t = self.params.t;
        let t4 = t / 4;
        for i in 0..t4 {
            let start_index = i * 4;
            let mut t_0 = input[start_index];
            t_0.add_assign(&input[start_index + 1]);
            let mut t_1 = input[start_index + 2];
            t_1.add_assign(&input[start_index + 3]);
            let mut t_2 = input[start_index + 1];
            t_2.double_in_place();
            t_2.add_assign(&t_1);
            let mut t_3 = input[start_index + 3];
            t_3.double_in_place();
            t_3.add_assign(&t_0);
            let mut t_4 = t_1;
            t_4.double_in_place();
            t_4.double_in_place();
            t_4.add_assign(&t_3);
            let mut t_5 = t_0;
            t_5.double_in_place();
            t_5.double_in_place();
            t_5.add_assign(&t_2);
            let mut t_6 = t_3;
            t_6.add_assign(&t_5);
            let mut t_7 = t_2;
            t_7.add_assign(&t_4);
            input[start_index] = t_6;
            input[start_index + 1] = t_5;
            input[start_index + 2] = t_7;
            input[start_index + 3] = t_4;
        }
    }

    fn matmul_external(&self, input: &mut[F]) {
        let t = self.params.t;
        match t {
            2 => {
                // Matrix circ(2, 1)
                let sum = input[0] + input[1];
                input[0] += sum;
                input[1] += sum;
            }
            3 => {
                // Matrix circ(2, 1, 1)
                let sum = input[0] + input[1] + input[2];
                input[0] += sum;
                input[1] += sum;
                input[2] += sum;
            }
            // TODO: Uncomment. Only working with state sizes of 2 and 3 for now
            // 4 => {
            //     // Applying cheap 4x4 MDS matrix to each 4-element part of the state
            //     self.matmul_m4(input);
            // }
            // 8 | 12 | 16 | 20 | 24 => {
            //     // Applying cheap 4x4 MDS matrix to each 4-element part of the state
            //     self.matmul_m4(input);
            //
            //     // Applying second cheap matrix for t > 4
            //     let t4 = t / 4;
            //     let mut stored = [F::zero(); 4];
            //     for l in 0..4 {
            //         stored[l] = input[l];
            //         for j in 1..t4 {
            //             stored[l].add_assign(&input[4 * j + l]);
            //         }
            //     }
            //     for i in 0..input.len() {
            //         input[i].add_assign(&stored[i % 4]);
            //     }
            // }
            _ => {
                panic!()
            }
        }
    }

    // fn matmul_internal(&self, input: &mut[F], mat_internal_diag_m_1: &[F]) {
    fn matmul_internal(&self, input: &mut[F]) {
        let t = self.params.t;

        match t {
            2 => {
                // [2, 1]
                // [1, 3]
                let sum = input[0] + input[1];
                input[0] += sum;
                input[1].double_in_place();
                input[1] += sum;
            }
            3 => {
                // [2, 1, 1]
                // [1, 2, 1]
                // [1, 1, 3]
                let sum = input[0] + input[1] + input[2];
                input[0] += sum;
                input[1] += sum;
                input[2].double_in_place();
                input[2] += sum;
            }
            // TODO: Uncomment. Only working with state sizes of 2 and 3 for now
            // 4 | 8 | 12 | 16 | 20 | 24 => {
            //     // Compute input sum
            //     let mut sum = input[0];
            //     input
            //         .iter()
            //         .skip(1)
            //         .take(t-1)
            //         .for_each(|el| sum.add_assign(el));
            //     // Add sum + diag entry * element to each element
            //     for i in 0..input.len() {
            //         input[i].mul_assign(&mat_internal_diag_m_1[i]);
            //         input[i].add_assign(&sum);
            //     }
            // }
            _ => {
                panic!()
            }
        }
    }

    fn add_rc(&self, input: &[F], rc: &[F]) -> Vec<F> {
        input
            .iter()
            .zip(rc.iter())
            .map(|(a, b)| {
                *a + *b
            })
            .collect()
    }
}

/// Constraints version of Poseidon2 permutation for t=2 and t=3 only
pub fn Poseidon_permutation_constraints<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<LinearCombination<F>>,
    params: &Poseidon2Params<F>,
) -> Result<Vec<LinearCombination<F>>, R1CSError> {
    let t = params.t;
    assert!(t == 2 || t == 3);
    assert_eq!(input.len(), t);

    let mut output_vars = input;

    // Linear layer at beginning
    matmul_external_constraints(&mut output_vars, params);

    // Full rounds before partial
    for r in 0..params.rounds_f_beginning {
        apply_round_constants(&mut output_vars, &params.round_constants[r]);
        output_vars = apply_sbox_full(cs, &output_vars, params)?;
        matmul_external_constraints(&mut output_vars, params);
    }

    let p_end = params.rounds_f_beginning + params.rounds_p;
    // Partial rounds
    for r in params.rounds_f_beginning..p_end {
        output_vars[0] = output_vars[0].clone() + LinearCombination::from(params.round_constants[r][0]);
        output_vars[0] = sbox_p_constraints(cs, &output_vars[0], params)?;
        matmul_internal_constraints(&mut output_vars, params);
    }

    // Full rounds after partial
    for r in p_end..params.rounds {
        apply_round_constants(&mut output_vars, &params.round_constants[r]);
        output_vars = apply_sbox_full(cs, &output_vars, params)?;
        matmul_external_constraints(&mut output_vars, params);
    }
    Ok(output_vars)
}

pub fn Poseidon_permutation_gadget<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<bulletproofs::r1cs::Variable<F>>,
    params: &Poseidon2Params<F>,
    output: &[F],
) -> Result<(), R1CSError> {
    let width = params.t;
    assert_eq!(output.len(), width);

    let input_vars: Vec<LinearCombination<F>> = input.iter().map(|e| (*e).into()).collect();
    let permutation_output = Poseidon_permutation_constraints::<F, CS>(cs, input_vars, params)?;

    for i in 0..width {
        constrain_lc_with_scalar::<F, CS>(cs, permutation_output[i].to_owned(), output[i]);
    }

    Ok(())
}

fn apply_round_constants<F: PrimeField>(vars: &mut [LinearCombination<F>], round_constants: &[F]) {
    for (v, rc) in vars.iter_mut().zip(round_constants.iter()) {
        *v = v.clone() + LinearCombination::from(*rc);
    }
}

fn apply_sbox_full<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &[LinearCombination<F>],
    params: &Poseidon2Params<F>,
) -> Result<Vec<LinearCombination<F>>, R1CSError> {
    Ok(input.iter().map(|el| sbox_p_constraints(cs, el, params)).collect::<Result<Vec<_>, _>>()?)
}

fn sbox_p_constraints<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &LinearCombination<F>,
    params: &Poseidon2Params<F>,
) -> Result<LinearCombination<F>, R1CSError> {
    let d = params.d;
    let (_, _, x2_var) = cs.multiply(input.clone(), input.clone());
    match d {
        3 => {
            let (_, _, x3_var) = cs.multiply(x2_var.into(), input.clone());
            Ok(x3_var.into())
        }
        5 => {
            let (_, _, x4_var) = cs.multiply(x2_var.into(), x2_var.into());
            let (_, _, x5_var) = cs.multiply(x4_var.into(), input.clone());
            Ok(x5_var.into())
        }
        7 => {
            let (_, _, x4_var) = cs.multiply(x2_var.into(), x2_var.into());
            let (_, _, x6_var) = cs.multiply(x4_var.into(), x2_var.into());
            let (_, _, x7_var) = cs.multiply(x6_var.into(), input.clone());
            Ok(x7_var.into())
        }
        _ => Err(R1CSError::MissingAssignment),
    }
}

fn matmul_external_constraints<F: PrimeField>(input: &mut [LinearCombination<F>], params: &Poseidon2Params<F>) {
    let t = params.t;
    assert!(t == 2 || t == 3);
    match t {
        2 => {
            let sum = input[0].clone() + input[1].clone();
            input[0] = input[0].clone() + sum.clone();
            input[1] = input[1].clone() + sum;
        }
        3 => {
            let sum = input[0].clone() + input[1].clone() + input[2].clone();
            input[0] = input[0].clone() + sum.clone();
            input[1] = input[1].clone() + sum.clone();
            input[2] = input[2].clone() + sum;
        }
        _ => unreachable!(),
    }
}

fn matmul_internal_constraints<F: PrimeField>(input: &mut [LinearCombination<F>], params: &Poseidon2Params<F>) {
    let t = params.t;
    assert!(t == 2 || t == 3);
    match t {
        2 => {
            let sum = input[0].clone() + input[1].clone();
            input[0] = input[0].clone() + sum.clone();
            let double = input[1].clone() * F::from(2u64);
            input[1] = double + sum;
        }
        3 => {
            let sum = input[0].clone() + input[1].clone() + input[2].clone();
            input[0] = input[0].clone() + sum.clone();
            input[1] = input[1].clone() + sum.clone();
            let double = input[2].clone() * F::from(2u64);
            input[2] = double + sum;
        }
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;
    use super::*;
    use ark_std::UniformRand;
    use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use dock_crypto_utils::transcript::MerlinTranscript;
    use ark_pallas::Affine as PallasA;
    use ark_pallas::Fr;
    use ark_serialize::CanonicalSerialize;
    #[test]
    fn test_poseidon2_perm_sbox() {
        let mut rng = rand::thread_rng();
        
        let width = 3;
        let d = 3;
        let full_rounds = 8;
        let partial_rounds = 56;
        
        let mat_internal_diag_m_1: Vec<Fr> = (0..width).map(|_| Fr::rand(&mut rng)).collect();
        let mat_internal: Vec<Vec<Fr>> = (0..width).map(|_| (0..width).map(|_| Fr::rand(&mut rng)).collect()).collect();
        let round_constants: Vec<Vec<Fr>> = (0..(full_rounds + partial_rounds)).map(|_| (0..width).map(|_| Fr::rand(&mut rng)).collect()).collect();
        
        let params = Poseidon2Params::<Fr>::new(width, d, full_rounds, partial_rounds, &mat_internal_diag_m_1, &mat_internal, &round_constants);
        
        let poseidon2 = Poseidon2::new(params.clone());
        
        let input = (0..width).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();
        
        let expected_output = poseidon2.permutation(&input);
        
        let pc_gens = PedersenGens::<PallasA>::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let (proof, commitments) = {
            let mut prover_transcript = MerlinTranscript::new(b"Poseidon2_perm_sbox");
            let mut prover = Prover::new(&pc_gens, prover_transcript);

            let mut comms = vec![];
            let mut vars = vec![];
            for i in 0..width {
                let (com, var) = prover.commit(input[i], Fr::rand(&mut rng));
                comms.push(com);
                vars.push(var);
            }

            let start = Instant::now();
            assert!(Poseidon_permutation_gadget(
                &mut prover,
                vars.clone(),
                &params,
                &expected_output
            ).is_ok());

            println!(
                "For Poseidon2 perm width={width} full rounds {full_rounds}, partial rounds {partial_rounds}, no of constraints is {}",
                &prover.number_of_constraints()
            );

            let proof = prover.prove(&bp_gens).unwrap();

            println!("Proving time is {:?} and size is {}", start.elapsed(), proof.compressed_size());
            (proof, comms)
        };

        let mut verifier_transcript = MerlinTranscript::new(b"Poseidon2_perm_sbox");
        let mut verifier = Verifier::new(verifier_transcript);

        let mut vars = vec![];
        for i in 0..width {
            let v = verifier.commit(commitments[i]);
            vars.push(v);
        }

        let start = Instant::now();
        assert!(Poseidon_permutation_gadget(
            &mut verifier,
            vars,
            &params,
            &expected_output
        ).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        println!("Verification time is {:?}", start.elapsed());
    }
}