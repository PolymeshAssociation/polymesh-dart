// The native implementation is taken from here https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon/poseidon.rs
// Following Appendix B of the paper and https://extgit.isec.tugraz.at/krypto/hadeshash/-/blob/master/code/poseidonperm_x3_64_24_optimized.sage

use std::ops::Range;
use ark_ff::{Field, PrimeField};
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, LinearCombination};
use bulletproofs::r1cs::constraint_system::constrain_lc_with_scalar;
use crate::poseidon_impls::poseidon_old::{SboxType, PoseidonParams as UnoptParams};
use crate::poseidon_impls::utils;

pub struct PoseidonParams<F: Field> {
    pub base: UnoptParams<F>,
    pub opt_round_constants: Vec<Vec<F>>,
    pub w_hat: Vec<Vec<F>>,
    pub v: Vec<Vec<F>>,
    pub m_i: Vec<Vec<F>>
}

impl<F: Field> PoseidonParams<F> {
    pub fn new(width: usize, full_rounds: usize, partial_rounds: usize) -> PoseidonParams<F> {
        let base = UnoptParams::new(width, full_rounds, partial_rounds);
        let (m_i, v, w_hat) = Self::equivalent_matrices(&base.MDS_matrix, width, partial_rounds);
        let opt_round_constants = Self::equivalent_round_constants(&base.round_constants, &base.MDS_matrix, full_rounds/2, partial_rounds);
        Self {
            base,
            opt_round_constants,
            w_hat,
            v,
            m_i
        }
    }

    pub fn equivalent_matrices(
        mds: &[Vec<F>],
        width: usize,
        rounds_p: usize,
    ) -> (Vec<Vec<F>>, Vec<Vec<F>>, Vec<Vec<F>>) {
        let mut w_hat = Vec::with_capacity(rounds_p);
        let mut v = Vec::with_capacity(rounds_p);
        let mut m_i = vec![vec![F::zero(); width]; width];

        let mds_ = utils::mat_transpose(mds);
        let mut m_mul = mds_.clone();

        for _ in 0..rounds_p {
            // calc m_hat, w and v
            let mut m_hat = vec![vec![F::zero(); width - 1]; width - 1];
            let mut w = vec![F::zero(); width - 1];
            let mut v_ = vec![F::zero(); width - 1];
            v_[..(width - 1)].clone_from_slice(&m_mul[0][1..width]);
            for row in 1..width {
                for col in 1..width {
                    m_hat[row - 1][col - 1] = m_mul[row][col];
                }
                w[row - 1] = m_mul[row][0];
            }
            // calc_w_hat
            let m_hat_inv = utils::mat_inverse(&m_hat);
            let w_hat_ = utils::mat_vec_mul(&m_hat_inv, &w);

            w_hat.push(w_hat_);
            v.push(v_);

            // update m_i
            m_i = m_mul.clone();
            m_i[0][0] = F::one();
            for i in 1..width {
                m_i[0][i] = F::zero();
                m_i[i][0] = F::zero();
            }
            m_mul = utils::mat_mat_mul(&mds_, &m_i);
        }

        (utils::mat_transpose(&m_i), v, w_hat)
    }

    pub fn equivalent_round_constants(
        round_constants: &[Vec<F>],
        mds: &[Vec<F>],
        rounds_f_beginning: usize,
        rounds_p: usize,
    ) -> Vec<Vec<F>> {
        let mut opt = vec![Vec::new(); rounds_p];
        let mds_inv = utils::mat_inverse(mds);

        let p_end = rounds_f_beginning + rounds_p - 1;
        let mut tmp = round_constants[p_end].clone();
        for i in (0..rounds_p - 1).rev() {
            let inv_cip = utils::mat_vec_mul(&mds_inv, &tmp);
            opt[i + 1] = vec![inv_cip[0]];
            tmp = round_constants[rounds_f_beginning + i].clone();
            for i in 1..inv_cip.len() {
                tmp[i] += inv_cip[i];
            }
        }
        opt[0] = tmp;

        opt
    }

    pub fn cheap_matmul(&self, input: &[F], r: usize) -> Vec<F> {
        let v = &self.v[r];
        let w_hat = &self.w_hat[r];
        let width = self.base.width;
        let mut new_state = vec![F::zero(); width];
        new_state[0] = self.base.MDS_matrix[0][0] * input[0];
        for i in 1..width {
            new_state[0] += w_hat[i - 1] * input[i];
        }
        for i in 1..width {
            new_state[i] += input[i] + (input[0] * v[i - 1])
        }
        new_state
    }


    pub fn get_total_rounds(&self) -> usize {
        self.base.full_rounds + self.base.partial_rounds
    }
}

pub fn Poseidon_permutation<F: PrimeField>(
    input: &[F],
    params: &PoseidonParams<F>,
    sbox: &SboxType<F>
) -> Vec<F> {
    let width = params.base.width;
    assert_eq!(input.len(), width);

    // Helper functions
    fn add_rc<F: Field>(input: &[F], rc: &[F]) -> Vec<F> {
        input.iter().zip(rc.iter()).map(|(a, b)| {
            *a + *b
        }).collect()
    }
    fn sbox_full<F: Field>(input: &[F], sbox: &SboxType<F>) -> Vec<F> {
        input.iter().map(|i| sbox.apply_sbox(*i)).collect()
    }
    fn sbox_partial<F: Field>(input: F, sbox: &SboxType<F>) -> F {
        sbox.apply_sbox(input)
    }

    let mut current_state = input.to_owned();
    let rounds_f_beginning = params.base.full_rounds / 2;
    let rounds_p = params.base.partial_rounds;
    let total_rounds = params.base.full_rounds + params.base.partial_rounds;
    let p_end = rounds_f_beginning + rounds_p;

    // Helper for full rounds
    fn poseidon_full_rounds<F: Field>(
        state: &mut Vec<F>,
        params: &PoseidonParams<F>,
        sbox: &SboxType<F>,
        range: Range<usize>
    ) {
        for r in range {
            *state = add_rc(state, &params.base.round_constants[r]);
            *state = sbox_full(state, sbox);
            *state = utils::mat_vec_mul(&params.base.MDS_matrix, state);
            println!("After round {r}: {:?}", state);
        }
    }

    println!("Optimz poseidon permutation");
    println!("init: {:?}", current_state);

    // Full rounds before partial
    poseidon_full_rounds(&mut current_state, params, sbox, 0..rounds_f_beginning);

    current_state = add_rc(&current_state, &params.opt_round_constants[0]);
    current_state = utils::mat_vec_mul(&params.m_i, &current_state);

    // Partial rounds
    for r in rounds_f_beginning..p_end {
        current_state[0] = sbox_partial(current_state[0], sbox);
        if r < p_end - 1 {
            current_state[0].add_assign(
                &params.opt_round_constants[r + 1 - rounds_f_beginning][0],
            );
        }
        current_state = params.cheap_matmul(&current_state, p_end - r - 1);
        println!("After round {r}: {:?}", current_state);
    }

    // Full rounds after partial
    poseidon_full_rounds(&mut current_state, params, sbox, p_end..total_rounds);
    current_state
}

/// Constraints version of Poseidon_permutation for optimized params
pub fn Poseidon_permutation_constraints<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<LinearCombination<F>>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
) -> Result<Vec<LinearCombination<F>>, R1CSError> {
    let width = params.base.width;
    assert_eq!(input.len(), width);

    let mut output_vars: Vec<LinearCombination<F>> = input;
    let rounds_f_beginning = params.base.full_rounds / 2;
    let rounds_p = params.base.partial_rounds;
    let total_rounds = params.base.full_rounds + params.base.partial_rounds;
    let p_end = rounds_f_beginning + rounds_p;

    fn apply_round_constants<F: PrimeField>(vars: &mut [LinearCombination<F>], round_constants: &[F]) {
        for (v, rc) in vars.iter_mut().zip(round_constants.iter()) {
            *v = v.clone() + LinearCombination::<F>::from(*rc);
        }
    }

    fn apply_sbox_full<F: PrimeField, CS: ConstraintSystem<F>>(
        cs: &mut CS,
        output_vars: &mut [LinearCombination<F>],
        sbox_type: &SboxType<F>,
    ) -> Result<Vec<LinearCombination<F>>, R1CSError> {
        let width = output_vars.len();
        let mut sbox_outputs = vec![LinearCombination::<F>::default(); width];
        for i in 0..width {
            sbox_outputs[i] = sbox_type
                .synthesize_sbox(cs, output_vars[i].clone(), F::zero())?
                .into();
        }
        Ok(sbox_outputs)
    }

    // Matrix multiplication helper for constraints
    fn mat_vec_mul<F: PrimeField>(mat: &[Vec<F>], vec: &[LinearCombination<F>]) -> Vec<LinearCombination<F>> {
        let width = vec.len();
        let mut out = vec![LinearCombination::<F>::default(); width];
        for i in 0..width {
            for j in 0..width {
                out[i] = out[i].clone() + vec[j].clone() * mat[i][j];
            }
        }
        out
    }

    pub fn cheap_matmul_constraints<F: PrimeField>(output_vars: &[LinearCombination<F>], params: &PoseidonParams<F>, r: usize) -> Vec<LinearCombination<F>> {
        let v = &params.v[r];
        let w_hat = &params.w_hat[r];
        let width = params.base.width;
        let mut new_state = vec![LinearCombination::<F>::default(); width];
        new_state[0] = output_vars[0].clone() * params.base.MDS_matrix[0][0];
        for i in 1..width {
            new_state[0] = new_state[0].clone() + output_vars[i].clone() * w_hat[i - 1];
        }
        for i in 1..width {
            new_state[i] = output_vars[i].clone() + (output_vars[0].clone() * v[i - 1]);
        }
        new_state
    }

    // Full rounds before partial
    for r in 0..rounds_f_beginning {
        apply_round_constants(&mut output_vars, &params.base.round_constants[r]);
        let sbox_outputs = apply_sbox_full(cs, &mut output_vars, sbox_type)?;
        output_vars = mat_vec_mul(&params.base.MDS_matrix, &sbox_outputs);
    }

    // Optimized partial rounds
    output_vars = mat_vec_mul(&params.m_i, &output_vars);
    apply_round_constants(&mut output_vars, &params.opt_round_constants[0]);

    for r in rounds_f_beginning..p_end {
        let mut sbox_outputs = output_vars.clone();
        sbox_outputs[0] = sbox_type
            .synthesize_sbox(cs, output_vars[0].clone(), F::zero())?
            .into();
        output_vars = sbox_outputs;
        if r < p_end - 1 {
            output_vars[0] = output_vars[0].clone() + LinearCombination::<F>::from(params.opt_round_constants[r + 1 - rounds_f_beginning][0]);
        }
        output_vars = cheap_matmul_constraints(&output_vars, params, p_end - r - 1);
    }

    // Full rounds after partial
    for r in p_end..total_rounds {
        apply_round_constants(&mut output_vars, &params.base.round_constants[r]);
        let sbox_outputs = apply_sbox_full(cs, &mut output_vars, sbox_type)?;
        output_vars = mat_vec_mul(&params.base.MDS_matrix, &sbox_outputs);
    }

    Ok(output_vars)
}

pub fn Poseidon_permutation_gadget<F: PrimeField, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    input: Vec<bulletproofs::r1cs::Variable<F>>,
    params: &PoseidonParams<F>,
    sbox_type: &SboxType<F>,
    output: &[F],
) -> Result<(), R1CSError> {
    let width = params.base.width;
    assert_eq!(output.len(), width);

    let input_vars: Vec<LinearCombination<F>> = input.iter().map(|e| (*e).into()).collect();
    let permutation_output = Poseidon_permutation_constraints::<F, CS>(cs, input_vars, params, sbox_type)?;

    for i in 0..width {
        constrain_lc_with_scalar::<F, CS>(cs, permutation_output[i].to_owned(), output[i]);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use std::time::Instant;
    use super::*;
    use ark_std::UniformRand;
    use crate::poseidon_impls::poseidon_old::SboxType;
    use bulletproofs::r1cs::{ConstraintSystem, Prover, Verifier};
    use bulletproofs::{BulletproofGens, PedersenGens};
    use dock_crypto_utils::transcript::MerlinTranscript;
    use ark_pallas::Affine as PallasA;
    use ark_pallas::Fr;
    use ark_serialize::CanonicalSerialize;

    #[ignore]
    #[test]
    fn test_poseidon_perm_optimz_cube_sbox() {
        let mut rng = rand::thread_rng();
        let width = 6;
        let full_rounds = 8;
        let partial_rounds = 140;
        let params = PoseidonParams::<Fr>::new(width, full_rounds, partial_rounds);
        let sbox_type = SboxType::Cube(std::marker::PhantomData);

        let input = (0..width).map(|_| Fr::rand(&mut rng)).collect::<Vec<_>>();
        let expected_output = Poseidon_permutation(&input, &params, &sbox_type);
        // assert_eq!(expected_output, crate::poseidon_impls::poseidon_old::Poseidon_permutation(&input, &params.base, &sbox_type));

        let pc_gens = PedersenGens::<PallasA>::default();
        let bp_gens = BulletproofGens::new(2048, 1);

        // Prover side
        let (proof, commitments) = {
            let prover_transcript = MerlinTranscript::new(b"Poseidon_perm_cube_optimz");
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
                &sbox_type,
                &expected_output
            ).is_ok());

            println!(
                "For Poseidon optimized perm width={width} full rounds {full_rounds}, partial rounds {partial_rounds}, no of constraints is {}",
                &prover.number_of_constraints()
            );

            let proof = prover.prove(&bp_gens).unwrap();

            println!("Proving time is {:?} and size is {}", start.elapsed(), proof.compressed_size());

            (proof, comms)
        };

        // Verifier side
        let verifier_transcript = MerlinTranscript::new(b"Poseidon_perm_cube_optimz");
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
            &sbox_type,
            &expected_output
        ).is_ok());

        assert!(verifier.verify(&proof, &pc_gens, &bp_gens).is_ok());
        println!("Verification time is {:?}", start.elapsed());
    }
}