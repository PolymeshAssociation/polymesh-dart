use ark_crypto_primitives::sponge::DuplexSpongeMode;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use crate::poseidon_impls::fp_var::FpVar;

/// the gadget for Poseidon sponge
///
/// This implementation of Poseidon is entirely from Fractal's implementation in [COS20][cos]
/// with small syntax changes.
///
/// [cos]: https://eprint.iacr.org/2019/1076
#[derive(Clone)]
pub struct PoseidonSpongeVar<F: PrimeField> {
    /// Constraint system
    pub cs: ConstraintSystemRef<F>,

    /// Sponge Parameters
    pub parameters: PoseidonConfig<F>,

    // Sponge State
    /// The sponge's state
    pub state: Vec<FpVar<F>>,
    /// The mode
    pub mode: DuplexSpongeMode,
}

impl<F: PrimeField> PoseidonSpongeVar<F> {
    fn apply_s_box(
        &self,
        state: &mut [FpVar<F>],
        is_full_round: bool,
    ) -> Result<(), SynthesisError> {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for state_item in state.iter_mut() {
                *state_item = state_item.pow_by_constant(&[self.parameters.alpha])?;
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the first element of state
        else {
            state[0] = state[0].pow_by_constant(&[self.parameters.alpha])?;
        }

        Ok(())
    }

    fn apply_ark(&self, state: &mut [FpVar<F>], round_number: usize) -> Result<(), SynthesisError> {
        for (i, state_elem) in state.iter_mut().enumerate() {
            *state_elem += self.parameters.ark[round_number][i];
        }
        Ok(())
    }

    fn apply_mds(&self, state: &mut [FpVar<F>]) -> Result<(), SynthesisError> {
        let mut new_state = Vec::new();
        let zero = FpVar::<F>::zero();
        for i in 0..state.len() {
            let mut cur = zero.clone();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem * self.parameters.mds[i][j];
                cur += &term;
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()]);
        Ok(())
    }

    fn permute(&mut self) -> Result<(), SynthesisError> {
        let full_rounds_over_2 = self.parameters.full_rounds / 2;
        let mut state = self.state.clone();
        for i in 0..full_rounds_over_2 {
            self.apply_ark(&mut state, i)?;
            self.apply_s_box(&mut state, true)?;
            self.apply_mds(&mut state)?;
        }
        for i in full_rounds_over_2..(full_rounds_over_2 + self.parameters.partial_rounds) {
            self.apply_ark(&mut state, i)?;
            self.apply_s_box(&mut state, false)?;
            self.apply_mds(&mut state)?;
        }

        for i in (full_rounds_over_2 + self.parameters.partial_rounds)
            ..(self.parameters.partial_rounds + self.parameters.full_rounds)
        {
            self.apply_ark(&mut state, i)?;
            self.apply_s_box(&mut state, true)?;
            self.apply_mds(&mut state)?;
        }

        self.state = state;
        Ok(())
    }
}