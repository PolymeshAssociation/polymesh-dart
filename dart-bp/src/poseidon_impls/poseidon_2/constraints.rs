//! R1CS constraints for the Poseidon2 permutation and 2:1 hash.

use super::{Poseidon2Params, ZERO_CONST};
use crate::error::{Error, Result};
use ark_ff::PrimeField;
use ark_std::borrow::ToOwned;
use ark_std::{vec, vec::Vec};
use bulletproofs::r1cs::constraint_system::constrain_lc_with_scalar;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, R1CSError, Variable};

/// Constraints version of Poseidon2 permutation for t=2 and t=3 only
pub fn Poseidon_permutation_constraints<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<LinearCombination<F>>,
    params: &Poseidon2Params<F>,
) -> Result<Vec<LinearCombination<F>>> {
    let t = params.state_size as usize;
    if input.len() != t {
        return Err(Error::UnequalInputSizeAndStateSize(input.len(), t));
    }

    let mut output_vars = input;

    // Linear layer at beginning
    matmul_external_constraints(&mut output_vars, params);

    // Full rounds before partial
    for r in 0..params.rounds_f_beginning as usize {
        apply_round_constants(&mut output_vars, &params.round_constants[r]);
        output_vars = apply_sbox_full(cs, &output_vars, params)?;
        matmul_external_constraints(&mut output_vars, params);
        for i in 0..t {
            output_vars[i] = core::mem::take(&mut output_vars[i]).simplify();
        }
    }

    let p_end = params.rounds_f_beginning as usize + params.rounds_p as usize;
    // Partial rounds
    for r in params.rounds_f_beginning as usize..p_end {
        output_vars[0] += params.round_constants[r][0];
        output_vars[0] = sbox_p_constraints(cs, &output_vars[0], params)?;
        matmul_internal_constraints(&mut output_vars, params);
        for i in 0..t {
            output_vars[i] = core::mem::take(&mut output_vars[i]).simplify();
        }
    }

    // Full rounds after partial
    for r in p_end..params.rounds as usize {
        apply_round_constants(&mut output_vars, &params.round_constants[r]);
        output_vars = apply_sbox_full(cs, &output_vars, params)?;
        matmul_external_constraints(&mut output_vars, params);
        for i in 0..t {
            output_vars[i] = core::mem::take(&mut output_vars[i]).simplify();
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
    let width = params.state_size as usize;
    if input.len() != width {
        return Err(Error::UnequalInputSizeAndStateSize(input.len(), width));
    }
    if output.len() != width {
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
        *v += *rc;
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
    let t = params.state_size as usize;
    debug_assert!(t == 2 || t == 3);
    match t {
        2 => {
            let mut sum = input[0].clone();
            sum += &input[1];
            input[0] += &sum;
            input[1] += sum;
        }
        3 => {
            let mut sum = input[0].clone();
            sum += &input[1];
            sum += &input[2];
            input[0] += &sum;
            input[1] += &sum;
            input[2] += sum;
        }
        _ => unreachable!(),
    }
}

fn matmul_internal_constraints<F: PrimeField>(
    input: &mut [LinearCombination<F>],
    params: &Poseidon2Params<F>,
) {
    let t = params.state_size as usize;
    debug_assert!(t == 2 || t == 3);
    match t {
        2 => {
            let mut sum = input[0].clone();
            sum += &input[1];
            input[0] += &sum;
            input[1] *= F::from(2u64);
            input[1] += sum;
        }
        3 => {
            let mut sum = input[0].clone();
            sum += &input[1];
            sum += &input[2];
            input[0] += &sum;
            input[1] += &sum;
            input[2] *= F::from(2u64);
            input[2] += sum;
        }
        _ => unreachable!(),
    }
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
    use crate::poseidon_impls::poseidon_2::params::pallas::get_poseidon2_params_for_2_1_hashing;
    use crate::poseidon_impls::poseidon_2::{Poseidon_hash_2_simple, Poseidon2};
    use ark_pallas::Affine as PallasA;
    use ark_pallas::Fr;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use bulletproofs::r1cs::{Prover, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use dock_crypto_utils::transcript::MerlinTranscript;
    use rand_core::CryptoRngCore;
    use std::time::Instant;

    fn poseidon2_perm_sbox<R: CryptoRngCore>(
        rng: &mut R,
        degree: usize,
        full_rounds: usize,
        partial_rounds: usize,
        transcript_label: &'static [u8],
    ) {
        let width = 3;

        let params = get_poseidon2_params_for_2_1_hashing().unwrap();

        let poseidon2 = Poseidon2::new(params);

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
                &prover.num_multipliers()
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
        full_rounds: usize,
        partial_rounds: usize,
        transcript_label: &'static [u8],
    ) {
        let params = get_poseidon2_params_for_2_1_hashing().unwrap();

        let xl = Fr::rand(rng);
        let xr = Fr::rand(rng);
        let expected_output = Poseidon_hash_2_simple(xl, xr, params).unwrap();

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
                &prover.num_multipliers()
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
        poseidon2_hash_2_simple(&mut rng, 8, 56, b"Poseidon_hash_2_quint");
    }
}
