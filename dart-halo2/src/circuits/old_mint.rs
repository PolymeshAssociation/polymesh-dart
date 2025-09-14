use core::marker::PhantomData;
use ff::PrimeField;
use halo2_proofs::circuit::{Layouter, Region, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Error, Precommitted, Selector};
use halo2_proofs::poly::Rotation;

// Precommitted column indices for randomness relation circuit
pub const PRECOMMITTED_INITIAL_RHO_IDX: usize = 0;
pub const PRECOMMITTED_OLD_CURRENT_RHO_IDX: usize = 1;
pub const PRECOMMITTED_NEW_CURRENT_RHO_IDX: usize = 2;
pub const PRECOMMITTED_OLD_RANDOMNESS_IDX: usize = 3;
pub const PRECOMMITTED_NEW_RANDOMNESS_IDX: usize = 4;

#[derive(Clone, Debug)]
pub struct MintChipConfig {
    pub precommitted: Column<Precommitted>,
    pub product: Selector,
    pub square: Selector,
}

pub struct MintChip<F: PrimeField> {
    config: MintChipConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> MintChip<F> {
    pub fn construct(config: MintChipConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MintChipConfig {
        let precommitted = meta.precommitted_column();
        let product = meta.selector();
        let square = meta.selector();

        meta.create_gate("product", |meta| {
            let s = meta.query_selector(product);
            let initial_row = meta.query_precommitted(precommitted, Rotation::cur());
            let old_rho = meta.query_precommitted(precommitted, Rotation::next());
            let new_rho = meta.query_precommitted(precommitted, Rotation(2));
            vec![s * (new_rho - (initial_row * old_rho))]
        });

        meta.create_gate("square", |meta| {
            let s = meta.query_selector(square);
            let old_randomness = meta.query_precommitted(precommitted, Rotation::cur());
            let new_randomness = meta.query_precommitted(precommitted, Rotation::next());
            vec![s * (new_randomness - old_randomness.square())]
        });

        MintChipConfig {
            precommitted,
            product,
            square,
        }
    }

    pub fn assign(
        &self,
        mut region: Region<'_, F>,
        initial_rho: Value<F>,
        old_current_rho: Value<F>,
        new_current_rho: Value<F>,
        old_randomness: Value<F>,
        new_randomness: Value<F>,
    ) -> Result<(), Error> {
        let config = &self.config;
        config.product.enable(&mut region, 0)?;
        region.assign_precommitted(|| "initial_rho", config.precommitted, 0, || initial_rho)?;
        region.assign_precommitted(
            || "old_current_rho",
            config.precommitted,
            1,
            || old_current_rho,
        )?;
        region.assign_precommitted(
            || "new_current_rho",
            config.precommitted,
            2,
            || new_current_rho,
        )?;

        config.square.enable(&mut region, 3)?;
        region.assign_precommitted(
            || "old_randomness",
            config.precommitted,
            3,
            || old_randomness,
        )?;
        region.assign_precommitted(
            || "new_randomness",
            config.precommitted,
            4,
            || new_randomness,
        )?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct MintCircuit<F: PrimeField> {
    pub initial_rho: Value<F>,
    pub old_current_rho: Value<F>,
    pub new_current_rho: Value<F>,
    pub old_randomness: Value<F>,
    pub new_randomness: Value<F>,
}

impl<F: PrimeField> Default for MintCircuit<F> {
    fn default() -> Self {
        Self::new(
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
        )
    }
}

impl<F: PrimeField> MintCircuit<F> {
    pub fn new(
        initial_rho: Value<F>,
        old_current_rho: Value<F>,
        new_current_rho: Value<F>,
        old_randomness: Value<F>,
        new_randomness: Value<F>,
    ) -> Self {
        Self {
            initial_rho,
            old_current_rho,
            new_current_rho,
            old_randomness,
            new_randomness,
        }
    }
}

impl<F: PrimeField> Circuit<F> for MintCircuit<F> {
    type Config = MintChipConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MintChip::<F>::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = MintChip::<F>::construct(config);
        layouter.assign_region(
            || "randomness-refresh",
            |region| {
                chip.assign(
                    region,
                    self.initial_rho,
                    self.old_current_rho,
                    self.new_current_rho,
                    self.old_randomness,
                    self.new_randomness,
                )
            },
        )
    }
}

#[derive(Clone, Debug)]
pub struct MintChipAltConfig {
    pub precommitted: Column<Precommitted>,
    pub product: Selector,
}

pub struct MintChipAlt<F: PrimeField> {
    config: MintChipAltConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> MintChipAlt<F> {
    pub fn construct(config: MintChipAltConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> MintChipAltConfig {
        let precommitted = meta.precommitted_column();
        let product = meta.selector();
        meta.enable_equality(precommitted);

        meta.create_gate("product", |meta| {
            let s = meta.query_selector(product);
            let a = meta.query_precommitted(precommitted, Rotation::cur());
            let b = meta.query_precommitted(precommitted, Rotation::next());
            let c = meta.query_precommitted(precommitted, Rotation(2));
            vec![s * (c - (a * b))]
        });

        MintChipAltConfig {
            precommitted,
            product,
        }
    }

    pub fn assign(
        &self,
        mut region: Region<'_, F>,
        initial_rho: Value<F>,
        old_current_rho: Value<F>,
        new_current_rho: Value<F>,
        old_randomness: Value<F>,
        new_randomness: Value<F>,
    ) -> Result<(), Error> {
        let config = &self.config;
        config.product.enable(&mut region, 0)?;
        region.assign_precommitted(|| "initial_rho", config.precommitted, 0, || initial_rho)?;
        region.assign_precommitted(
            || "old_current_rho",
            config.precommitted,
            1,
            || old_current_rho,
        )?;
        region.assign_precommitted(
            || "new_current_rho",
            config.precommitted,
            2,
            || new_current_rho,
        )?;

        // Assign 2 consecutive cells both as old_randomness and the 3rd cell as new_randomness
        // and ensure both of previous cells are equal
        config.product.enable(&mut region, 3)?;
        let old_rand_1_cell = region.assign_precommitted(
            || "old_randomness_1",
            config.precommitted,
            3,
            || old_randomness,
        )?;
        let old_rand_2_cell = region.assign_precommitted(
            || "old_randomness_2",
            config.precommitted,
            4,
            || old_randomness,
        )?;
        region.assign_precommitted(
            || "new_randomness",
            config.precommitted,
            5,
            || new_randomness,
        )?;
        region.constrain_equal(old_rand_1_cell.cell(), old_rand_2_cell.cell())?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct MintCircuitAlt<F: PrimeField> {
    pub initial_rho: Value<F>,
    pub old_current_rho: Value<F>,
    pub new_current_rho: Value<F>,
    pub old_randomness: Value<F>,
    pub new_randomness: Value<F>,
}

impl<F: PrimeField> Default for MintCircuitAlt<F> {
    fn default() -> Self {
        Self::new(
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
        )
    }
}

impl<F: PrimeField> MintCircuitAlt<F> {
    pub fn new(
        initial_rho: Value<F>,
        old_current_rho: Value<F>,
        new_current_rho: Value<F>,
        old_randomness: Value<F>,
        new_randomness: Value<F>,
    ) -> Self {
        Self {
            initial_rho,
            old_current_rho,
            new_current_rho,
            old_randomness,
            new_randomness,
        }
    }
}

impl<F: PrimeField> Circuit<F> for MintCircuitAlt<F> {
    type Config = MintChipAltConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        MintChipAlt::<F>::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = MintChipAlt::<F>::construct(config);
        layouter.assign_region(
            || "randomness-refresh-alt",
            |region| {
                chip.assign(
                    region,
                    self.initial_rho,
                    self.old_current_rho,
                    self.new_current_rho,
                    self.old_randomness,
                    self.new_randomness,
                )
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use halo2_proofs::dev::{CircuitCost, CircuitGates, MockProver};
    use halo2_proofs::plonk::{SingleVerifier, create_proof_with_given_column_blindings, keygen_pk, keygen_vk, verify_proof, get_the_only_precommitted_col_comm};
    use halo2_proofs::poly::commitment::Params;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use pasta_curves::pallas;
    use rand_core::OsRng;
    use std::time::Instant;

    #[test]
    fn mock_mint() {
        let k = 5;
        let mut rng = OsRng;
        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();

        let circuit = MintCircuit::<pallas::Scalar>::new(
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
        );

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let gates = CircuitGates::collect::<_, MintCircuit<pallas::Scalar>>();
        println!("gates {}", gates);
        let cost = CircuitCost::<pallas::Point, MintCircuit<pallas::Scalar>>::measure(k, &circuit);
        println!("cost {:#?}", cost);
        let proof_size = cost.proof_size(1);
        println!("proof_size {:#?}", proof_size);

        // Fail if initial_rho is wrong
        let circuit = MintCircuit::<pallas::Scalar>::new(
            Value::known(initial_rho + pallas::Scalar::ONE),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
        );
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());

        // Fail if new_randomness is wrong
        let circuit = MintCircuit::<pallas::Scalar>::new(
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness + pallas::Scalar::ONE),
            Value::known(new_randomness),
        );
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn real_prover_mint() {
        let k = 5;
        let mut rng = OsRng;
        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();

        let empty_circuit = MintCircuit::<pallas::Scalar>::default();
        let params = Params::<pallas::Affine>::new(k);
        let vk = keygen_vk(&params, &empty_circuit).unwrap();
        let pk = keygen_pk(&params, vk, &empty_circuit).unwrap();

        let start = Instant::now();
        let circuit = MintCircuit::<pallas::Scalar>::new(
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
        );

        // TODO: Check if this is always correct since we consider only queries to advice columns but some circuits might
        // have no advice columns.
        let num_blindings = pk.get_vk().blinding_factors() + 2;
        let blinding_rows = (0..num_blindings)
            .map(|_| pallas::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof_with_given_column_blindings(
            &params,
            &pk,
            &[circuit],
            &[&[]],
            vec![Some(vec![blinding_rows.clone()])],
            &mut rng,
            &mut transcript,
        )
        .unwrap();
        let proof = transcript.finalize();
        println!("Proving time: {:?}", start.elapsed());
        println!("Proof size: {} bytes", proof.len());

        let start = Instant::now();
        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        verify_proof(&params, pk.get_vk(), strategy, &[&[]], &mut transcript).unwrap();
        println!("Verification time: {:?}", start.elapsed());

        // Verify commitment
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof.as_slice());
        let precommitted_commitment = get_the_only_precommitted_col_comm(pk.get_vk(), &mut transcript).unwrap();

        let domain = pk.get_vk().get_domain();

        let mut precommitted = domain.empty_lagrange();
        precommitted[PRECOMMITTED_INITIAL_RHO_IDX] = initial_rho;
        precommitted[PRECOMMITTED_OLD_CURRENT_RHO_IDX] = old_current_rho;
        precommitted[PRECOMMITTED_NEW_CURRENT_RHO_IDX] = new_current_rho;
        precommitted[PRECOMMITTED_OLD_RANDOMNESS_IDX] = old_randomness;
        precommitted[PRECOMMITTED_NEW_RANDOMNESS_IDX] = new_randomness;

        let usable_rows = params.n as usize - (num_blindings - 1);
        for (i, v) in precommitted[usable_rows..].iter_mut().enumerate() {
            *v = blinding_rows[i];
        }
        let comm = params
            .commit_lagrange(&precommitted, (*blinding_rows.last().unwrap()).into())
            .into();
        assert_eq!(precommitted_commitment, comm);
    }

    #[test]
    fn mock_mint_alt() {
        let k = 5;
        let mut rng = OsRng;
        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();

        let circuit = MintCircuitAlt::<pallas::Scalar>::new(
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
        );

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();

        let gates = CircuitGates::collect::<_, MintCircuitAlt<pallas::Scalar>>();
        println!("gates {}", gates);
        let cost =
            CircuitCost::<pallas::Point, MintCircuitAlt<pallas::Scalar>>::measure(k, &circuit);
        println!("cost {:#?}", cost);
        let proof_size = cost.proof_size(1);
        println!("proof_size {:#?}", proof_size);

        // Fail if initial_rho is wrong
        let circuit = MintCircuitAlt::<pallas::Scalar>::new(
            Value::known(initial_rho + pallas::Scalar::ONE),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
        );
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());

        // Fail if new_randomness is wrong
        let circuit = MintCircuitAlt::<pallas::Scalar>::new(
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness + pallas::Scalar::ONE),
            Value::known(new_randomness),
        );
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn real_prover_mint_alt() {
        let k = 5;
        let mut rng = OsRng;
        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();

        let empty_circuit = MintCircuitAlt::<pallas::Scalar>::default();
        let params = Params::<pallas::Affine>::new(k);
        let vk = keygen_vk(&params, &empty_circuit).unwrap();
        let pk = keygen_pk(&params, vk, &empty_circuit).unwrap();

        let start = Instant::now();
        let circuit = MintCircuitAlt::<pallas::Scalar>::new(
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
        );

        // TODO: Check if this is always correct since we consider only queries to advice columns but some circuits might
        // have no advice columns.
        let num_blindings = pk.get_vk().blinding_factors() + 2;
        let blinding_rows = (0..num_blindings)
            .map(|_| pallas::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof_with_given_column_blindings(
            &params,
            &pk,
            &[circuit],
            &[&[]],
            vec![Some(vec![blinding_rows.clone()])],
            &mut rng,
            &mut transcript,
        )
        .unwrap();
        let proof = transcript.finalize();
        println!("Proving time: {:?}", start.elapsed());
        println!("Proof size: {} bytes", proof.len());

        let start = Instant::now();
        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        verify_proof(&params, pk.get_vk(), strategy, &[&[]], &mut transcript).unwrap();
        println!("Verification time: {:?}", start.elapsed());

        // Verify commitment
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof.as_slice());
        let precommitted_commitment = get_the_only_precommitted_col_comm(pk.get_vk(), &mut transcript).unwrap();

        let domain = pk.get_vk().get_domain();

        let mut precommitted = domain.empty_lagrange();
        precommitted[0] = initial_rho;
        precommitted[1] = old_current_rho;
        precommitted[2] = new_current_rho;
        precommitted[3] = old_randomness;
        precommitted[4] = old_randomness;
        precommitted[5] = new_randomness;

        let usable_rows = params.n as usize - (num_blindings - 1);
        for (i, v) in precommitted[usable_rows..].iter_mut().enumerate() {
            *v = blinding_rows[i];
        }
        let comm = params
            .commit_lagrange(&precommitted, (*blinding_rows.last().unwrap()).into())
            .into();
        assert_eq!(precommitted_commitment, comm);
    }
}
