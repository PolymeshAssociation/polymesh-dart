// The native implementation is taken from here https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2.rs

pub mod params;

use crate::error::{Error, Result};
use ark_ff::PrimeField;
use ark_std::borrow::ToOwned;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::constraint_system::constrain_lc_with_scalar;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, R1CSError, Variable};
pub use params::Poseidon2Params;

pub const ZERO_CONST: u64 = 0;

#[derive(Clone, Debug)]
pub struct Poseidon2<F: PrimeField> {
    pub params: Poseidon2Params<F>,
}

impl<F: PrimeField> Poseidon2<F> {
    pub fn new(params: Poseidon2Params<F>) -> Self {
        Poseidon2 { params }
    }

    pub fn get_t(&self) -> usize {
        self.params.state_size
    }

    pub fn permutation(&self, input: &[F]) -> Result<Vec<F>> {
        let t = self.params.state_size;
        if input.len() != t {
            return Err(Error::UnequalInputSizeAndStateSize(input.len(), t));
        }

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
        Ok(current_state)
    }

    fn sbox(&self, input: &[F]) -> Vec<F> {
        input.iter().map(|el| self.sbox_p(el)).collect()
    }

    fn sbox_p(&self, input: &F) -> F {
        let mut res = *input;
        res.square_in_place();

        match self.params.degree {
            3 => {
                res.mul_assign(input);
            }
            5 => {
                res.square_in_place();
                res.mul_assign(input);
            }
            7 => {
                let res_sq = res;
                res.square_in_place();
                res.mul_assign(&res_sq);
                res.mul_assign(input);
            }
            _ => {
                // This is unreachable because `Poseidon2Params` will never be initialized with such a degree
                // and the call to `Self::permutation` ensures that only degrees supported by `Poseidon2Params`
                // are accepted
                unreachable!()
            }
        }
        res
    }

    #[allow(dead_code)]
    fn matmul_m4(&self, input: &mut [F]) {
        let t = self.params.state_size;
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

    fn matmul_external(&self, input: &mut [F]) {
        let t = self.params.state_size;
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
                // This is unreachable because `Poseidon2Params` will never be initialized with such a state size
                // and the call to `Self::permutation` ensures that only state sizes supported by `Poseidon2Params`
                // are accepted
                unreachable!()
            }
        }
    }

    // fn matmul_internal(&self, input: &mut[F], mat_internal_diag_m_1: &[F]) {
    fn matmul_internal(&self, input: &mut [F]) {
        let t = self.params.state_size;

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
                // This is unreachable because `Poseidon2Params` will never be initialized with such a state size
                // and the call to `Self::permutation` ensures that only state sizes supported by `Poseidon2Params`
                // are accepted
                unreachable!()
            }
        }
    }

    fn add_rc(&self, input: &[F], rc: &[F]) -> Vec<F> {
        input.iter().zip(rc.iter()).map(|(a, b)| *a + *b).collect()
    }
}

/// Constraints version of Poseidon2 permutation for t=2 and t=3 only
pub fn Poseidon_permutation_constraints<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<LinearCombination<F>>,
    params: &Poseidon2Params<F>,
) -> Result<Vec<LinearCombination<F>>> {
    let t = params.state_size;
    if input.len() != t {
        return Err(Error::UnequalInputSizeAndStateSize(input.len(), t));
    }

    let mut output_vars = input;

    // Linear layer at beginning
    matmul_external_constraints(&mut output_vars, params);

    // Full rounds before partial
    for r in 0..params.rounds_f_beginning {
        apply_round_constants(&mut output_vars, &params.round_constants[r]);
        output_vars = apply_sbox_full(cs, &output_vars, params)?;
        matmul_external_constraints(&mut output_vars, params);
        for i in 0..t {
            output_vars[i] = output_vars[i].clone().simplify();
        }
    }

    let p_end = params.rounds_f_beginning + params.rounds_p;
    // Partial rounds
    for r in params.rounds_f_beginning..p_end {
        output_vars[0] =
            output_vars[0].clone() + LinearCombination::from(params.round_constants[r][0]);
        output_vars[0] = sbox_p_constraints(cs, &output_vars[0], params)?;
        matmul_internal_constraints(&mut output_vars, params);
        for i in 0..t {
            output_vars[i] = output_vars[i].clone().simplify();
        }
    }

    // Full rounds after partial
    for r in p_end..params.rounds {
        apply_round_constants(&mut output_vars, &params.round_constants[r]);
        output_vars = apply_sbox_full(cs, &output_vars, params)?;
        matmul_external_constraints(&mut output_vars, params);
        for i in 0..t {
            output_vars[i] = output_vars[i].clone().simplify();
        }
    }
    Ok(output_vars)
}

pub fn Poseidon_permutation_gadget<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<Variable<F>>,
    params: &Poseidon2Params<F>,
    output: &[F],
) -> Result<()> {
    let width = params.state_size;
    if input.len() != width {
        return Err(Error::UnequalInputSizeAndStateSize(output.len(), width));
    }

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
    Ok(input
        .iter()
        .map(|el| sbox_p_constraints(cs, el, params))
        .collect::<Result<Vec<_>, _>>()?)
}

fn sbox_p_constraints<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: &LinearCombination<F>,
    params: &Poseidon2Params<F>,
) -> Result<LinearCombination<F>, R1CSError> {
    let d = params.degree;
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

fn matmul_external_constraints<F: PrimeField>(
    input: &mut [LinearCombination<F>],
    params: &Poseidon2Params<F>,
) {
    let t = params.state_size;
    debug_assert!(t == 2 || t == 3);
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

fn matmul_internal_constraints<F: PrimeField>(
    input: &mut [LinearCombination<F>],
    params: &Poseidon2Params<F>,
) {
    let t = params.state_size;
    debug_assert!(t == 2 || t == 3);
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

pub fn Poseidon_hash_2_simple<F: PrimeField>(
    xl: F,
    xr: F,
    params: Poseidon2Params<F>,
) -> Result<F> {
    let poseidon2 = Poseidon2::new(params);
    poseidon2
        .permutation(&[xl, xr, F::from(ZERO_CONST)])
        .map(|x| x[0])
}

pub fn Poseidon_hash_2_constraints_simple<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    xl: LinearCombination<F>,
    xr: LinearCombination<F>,
    params: &Poseidon2Params<F>,
) -> Result<LinearCombination<F>> {
    let inputs = vec![xl, xr, LinearCombination::<F>::from(F::from(ZERO_CONST))];
    let permutation_output = Poseidon_permutation_constraints::<F, CS>(cs, inputs, params)?;
    Ok(permutation_output[0].to_owned())
}

pub fn Poseidon_hash_2_gadget_simple<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    xl: Variable<F>,
    xr: Variable<F>,
    params: &Poseidon2Params<F>,
    output: F,
) -> Result<()> {
    let hash = Poseidon_hash_2_constraints_simple::<F, CS>(cs, xl.into(), xr.into(), params)?;

    constrain_lc_with_scalar::<F, CS>(cs, hash, output);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::Affine as PallasA;
    use ark_pallas::Fr;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use bulletproofs::r1cs::{Prover, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use dock_crypto_utils::transcript::MerlinTranscript;
    use rand_core::CryptoRngCore;
    use std::time::Instant;
    use crate::poseidon_impls::poseidon_2::params::pallas::{MAT_DIAG3_M_1, MAT_INTERNAL3, RC3};

    fn poseidon2_perm_sbox<R: CryptoRngCore>(
        rng: &mut R,
        degree: usize,
        full_rounds: usize,
        partial_rounds: usize,
        transcript_label: &'static [u8],
    ) {
        let width = 3;

        let params = Poseidon2Params::<Fr>::new(width, degree, full_rounds, partial_rounds, MAT_DIAG3_M_1.as_ref().unwrap().to_vec(), MAT_INTERNAL3.as_ref().unwrap().to_vec(), RC3.as_ref().unwrap().to_vec()).unwrap();

        let poseidon2 = Poseidon2::new(params.clone());

        let input = (0..width).map(|_| Fr::rand(rng)).collect::<Vec<_>>();

        let expected_output = poseidon2.permutation(&input).unwrap();

        let pc_gens = PedersenGens::<PallasA>::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let (proof, commitment) = {
            let prover_transcript = MerlinTranscript::new(transcript_label);
            let mut prover = Prover::new(&pc_gens, prover_transcript);

            let start = Instant::now();
            let (comm, vars) = prover.commit_vec(&input, Fr::rand(rng), &bp_gens);

            assert!(
                Poseidon_permutation_gadget(&mut prover, vars.clone(), &params, &expected_output)
                    .is_ok()
            );

            println!(
                "For Poseidon2 perm width={width}, d={degree} full rounds {full_rounds}, partial rounds {partial_rounds}, no of constraints is {}",
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
        let vars = verifier.commit_vec(width, commitment);

        assert!(
            Poseidon_permutation_gadget(&mut verifier, vars, &params, &expected_output).is_ok()
        );

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        println!("Verification time is {:?}", start.elapsed());
    }

    fn poseidon2_hash_2_simple<R: CryptoRngCore>(
        rng: &mut R,
        degree: usize,
        full_rounds: usize,
        partial_rounds: usize,
        transcript_label: &'static [u8],
    ) {
        let width = 3;

        let params = Poseidon2Params::<Fr>::new(width, degree, full_rounds, partial_rounds, MAT_DIAG3_M_1.as_ref().unwrap().to_vec(), MAT_INTERNAL3.as_ref().unwrap().to_vec(), RC3.as_ref().unwrap().to_vec()).unwrap();

        let xl = Fr::rand(rng);
        let xr = Fr::rand(rng);
        let expected_output = Poseidon_hash_2_simple(xl, xr, params.clone()).unwrap();

        let pc_gens = PedersenGens::<PallasA>::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        let (proof, commitment) = {
            let prover_transcript = MerlinTranscript::new(transcript_label);
            let mut prover = Prover::new(&pc_gens, prover_transcript);

            let start = Instant::now();

            let (comm, mut vars) = prover.commit_vec(&[xl, xr], Fr::rand(rng), &bp_gens);

            assert!(
                Poseidon_hash_2_gadget_simple(
                    &mut prover,
                    vars.remove(0),
                    vars.remove(0),
                    &params,
                    expected_output
                )
                .is_ok()
            );

            println!(
                "For Poseidon2 hash 2:1 rounds {}, no of constraints is {}",
                full_rounds + partial_rounds,
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
                &params,
                expected_output
            )
            .is_ok()
        );

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());

        println!("Verification time is {:?}", start.elapsed());
    }

    #[test]
    fn test_poseidon2_perm_quint_sbox() {
        let mut rng = rand::thread_rng();
        poseidon2_perm_sbox(&mut rng, 5, 8, 56, b"Poseidon2_perm_2_quint_sbox");
    }

    #[test]
    fn test_poseidon2_hash_2_simple_quint_sbox() {
        let mut rng = rand::thread_rng();
        poseidon2_hash_2_simple(&mut rng, 5, 8, 56, b"Poseidon_hash_2_quint");
    }
}
