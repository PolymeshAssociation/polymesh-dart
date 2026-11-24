// The native implementation is taken from here https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2.rs

#[cfg(feature = "host_proofs")]
pub mod constraints;
pub mod params;

use crate::error::{Error, Result};
use ark_ff::PrimeField;
use ark_std::borrow::ToOwned;
use ark_std::vec::Vec;
pub use params::Poseidon2Params;

pub const ZERO_CONST: u64 = 0;

#[derive(Clone, Debug)]
pub struct Poseidon2<'a, F: PrimeField> {
    pub params: &'a Poseidon2Params<F>,
}

impl<'a, F: PrimeField> Poseidon2<'a, F> {
    pub fn new(params: &'a Poseidon2Params<F>) -> Self {
        Poseidon2 { params }
    }

    pub fn get_t(&self) -> usize {
        self.params.state_size as usize
    }

    pub fn permutation(&self, input: &[F]) -> Result<Vec<F>> {
        let t = self.params.state_size as usize;
        if input.len() != t {
            return Err(Error::UnequalInputSizeAndStateSize(input.len(), t));
        }

        let mut current_state = input.to_owned();

        // Linear layer at beginning
        self.matmul_external(&mut current_state);

        for r in 0..self.params.rounds_f_beginning as usize {
            self.add_rc(&mut current_state, &self.params.round_constants[r]);
            self.sbox(&mut current_state);
            self.matmul_external(&mut current_state);
        }

        let p_end = self.params.rounds_f_beginning as usize + self.params.rounds_p as usize;
        for r in self.params.rounds_f_beginning as usize..p_end {
            current_state[0].add_assign(&self.params.round_constants[r][0]);
            current_state[0] = self.sbox_p(&current_state[0]);
            // self.matmul_internal(&mut current_state, &self.params.mat_internal_diag_m_1);
            self.matmul_internal(&mut current_state);
        }

        for r in p_end..self.params.rounds as usize {
            self.add_rc(&mut current_state, &self.params.round_constants[r]);
            self.sbox(&mut current_state);
            self.matmul_external(&mut current_state);
        }
        Ok(current_state)
    }

    fn sbox(&self, state: &mut [F]) {
        for el in state.iter_mut() {
            *el = self.sbox_p(el);
        }
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
        let t = self.params.state_size as usize;
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
        let t = self.params.state_size as usize;
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
        let t = self.params.state_size as usize;

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

    fn add_rc(&self, state: &mut [F], rc: &[F]) {
        for (a, b) in state.iter_mut().zip(rc.iter()) {
            *a += b;
        }
    }
}

pub fn Poseidon_hash_2_simple<F: PrimeField>(
    xl: F,
    xr: F,
    params: &Poseidon2Params<F>,
) -> Result<F> {
    let poseidon2 = Poseidon2::new(params);
    poseidon2
        .permutation(&[xl, xr, F::from(ZERO_CONST)])
        .map(|x| x[0])
}

#[cfg(test)]
mod kats {
    use super::*;
    use crate::poseidon_impls::poseidon_2::params::pallas::{
        get_poseidon2_params_for_2_1_hashing, new_poseidon2_params_for_2_1_hashing,
    };
    use ark_pallas::Fr;

    fn fr(s: &str) -> Fr {
        let mut bytes = [0u8; 32];
        hex::decode_to_slice(s, &mut bytes).unwrap();
        Fr::from_be_bytes_mod_order(&bytes)
    }

    /// Known answer from `poseidon2_tests_vesta::kats` in
    /// [HorizenLabs poseidon2.rs](https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2.rs).
    /// Their Pallas and Vesta instances share the round constants and matrices. `ark_pallas::Fr` is
    /// their `FpVesta`, so the Vesta vector applies.
    #[test]
    fn matches_horizen_labs_kats() {
        let expected = [
            fr("261ecbdfd62c617b82d297705f18c788fc9831b14a6a2b8f61229bef68ce2792"),
            fr("2c76327e0b7653873263158cf8545c282364b183880fcdea93ca8526d518c66f"),
            fr("262316c0ce5244838c75873299b59d763ae0849d2dd31bdc95caf7db1c2901bf"),
        ];
        let input = [Fr::from(0u64), Fr::from(1u64), Fr::from(2u64)];
        for params in [
            get_poseidon2_params_for_2_1_hashing().unwrap(),
            &new_poseidon2_params_for_2_1_hashing().unwrap(),
        ] {
            assert_eq!(
                Poseidon2::new(params).permutation(&input).unwrap(),
                expected
            );
        }
    }
}
