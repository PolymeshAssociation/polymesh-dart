use core::marker::PhantomData;
use ff::{PrimeField, PrimeFieldBits};
use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheck;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Error, Expression, Instance, Precommitted, Selector, TableColumn};
use halo2_proofs::poly::Rotation;

pub const PRECOMMITTED_INITIAL_RHO_IDX: usize = 0;
pub const PRECOMMITTED_OLD_CURRENT_RHO_IDX: usize = 1;
pub const PRECOMMITTED_NEW_CURRENT_RHO_IDX: usize = 2;
pub const PRECOMMITTED_OLD_RANDOMNESS_IDX: usize = 3;
pub const PRECOMMITTED_NEW_RANDOMNESS_IDX: usize = 4;
pub const PRECOMMITTED_FLAG_IDX: usize = 5;
pub const PRECOMMITTED_OLD_BALANCE_IDX: usize = 6;
pub const PRECOMMITTED_AMOUNT_IDX: usize = 7;
pub const PRECOMMITTED_NEW_BALANCE_IDX: usize = 8;

#[derive(Clone, Copy)]
pub struct AffirmationWithBalanceChangeCircuit<
    F: PrimeFieldBits,
    Lookup: LookupRangeCheck<F, LIMB_BITS>,
    const LIMB_BITS: usize,
> {
    num_words: usize,
    initial_rho: Value<F>,
    old_current_rho: Value<F>,
    new_current_rho: Value<F>,
    old_randomness: Value<F>,
    new_randomness: Value<F>,
    amount: Value<F>,
    old_balance: Value<F>,
    new_balance: Value<F>,
    _marker: PhantomData<Lookup>,
}

#[derive(Clone)]
pub struct AffirmationWithBalanceChangeConfig<
    F: PrimeFieldBits,
    const LIMB_BITS: usize,
    Lookup: LookupRangeCheck<F, LIMB_BITS> + Clone,
> {
    pub precommitted: Column<Precommitted>,
    pub product: Selector,
    pub square: Selector,
    pub balance_change: Selector,
    pub instance: Column<Instance>,
    pub lookup_config: Lookup,
    pub table_idx: TableColumn,
    phantom: PhantomData<F>,
}

impl<F: PrimeFieldBits, Lookup: LookupRangeCheck<F, LIMB_BITS>, const LIMB_BITS: usize>
    AffirmationWithBalanceChangeCircuit<F, Lookup, LIMB_BITS>
{
    pub fn new(
        num_words: usize,
        initial_rho: Value<F>,
        old_current_rho: Value<F>,
        new_current_rho: Value<F>,
        old_randomness: Value<F>,
        new_randomness: Value<F>,
        amount: Value<F>,
        old_balance: Value<F>,
        new_balance: Value<F>,
    ) -> Self {
        Self {
            initial_rho,
            old_current_rho,
            new_current_rho,
            old_randomness,
            new_randomness,
            amount,
            old_balance,
            new_balance,
            num_words,
            _marker: PhantomData,
        }
    }
}

impl<F: PrimeFieldBits, Lookup: LookupRangeCheck<F, LIMB_BITS> + Clone, const LIMB_BITS: usize>
    Circuit<F> for AffirmationWithBalanceChangeCircuit<F, Lookup, LIMB_BITS>
{
    type Config = AffirmationWithBalanceChangeConfig<F, LIMB_BITS, Lookup>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(
            self.num_words,
            self.initial_rho,
            self.old_current_rho,
            self.new_current_rho,
            self.old_randomness,
            self.new_randomness,
            self.amount,
            self.old_balance,
            self.new_balance,
        )
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let precommitted = meta.precommitted_column();
        let product = meta.selector();
        let square = meta.selector();
        let balance_change = meta.selector();
        let instance = meta.instance_column();
        meta.enable_equality(precommitted);
        meta.enable_equality(instance);

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

        // Enforce new_balance = old_balance + (b - 1) * amount
        meta.create_gate("balance_change", |meta| {
            let s = meta.query_selector(balance_change);
            // Not enforcing if flag is an acceptable value since its instance and verifier should set it correctly
            let flag = meta.query_precommitted(precommitted, Rotation::cur());
            let old_balance = meta.query_precommitted(precommitted, Rotation::next());
            let amount = meta.query_precommitted(precommitted, Rotation(2));
            let new_balance = meta.query_precommitted(precommitted, Rotation(3));

            vec![s * (new_balance - old_balance - ((flag - Expression::Constant(F::ONE)) * amount))]
        });

        let running_sum = meta.advice_column();
        let table_idx = meta.lookup_table_column();
        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        let lookup_config = Lookup::configure(meta, running_sum, table_idx);

        AffirmationWithBalanceChangeConfig {
            precommitted,
            product,
            square,
            balance_change,
            instance,
            lookup_config,
            table_idx,
            phantom: PhantomData,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // Load table values for range check
        layouter.assign_table(
            || "table_idx",
            |mut table| {
                for index in 0..(1 << LIMB_BITS) {
                    table.assign_cell(
                        || "table_idx",
                        config.table_idx,
                        index,
                        || Value::known(F::from(index as u64)),
                    )?;
                }
                Ok(())
            },
        )?;

        let new_balance_cell = layouter.assign_region(
            || "affirmation-with-balance-change",
            |mut region| {
                // flag value will be read directly in the constraint through the instance column

                config.product.enable(&mut region, 0)?;
                region.assign_precommitted(|| "initial_rho", config.precommitted, PRECOMMITTED_INITIAL_RHO_IDX, || self.initial_rho)?;
                region.assign_precommitted(|| "old_current_rho", config.precommitted, PRECOMMITTED_OLD_CURRENT_RHO_IDX, || self.old_current_rho)?;
                region.assign_precommitted(|| "new_current_rho", config.precommitted, PRECOMMITTED_NEW_CURRENT_RHO_IDX, || self.new_current_rho)?;

                config.square.enable(&mut region, 3)?;
                region.assign_precommitted(|| "old_randomness", config.precommitted, PRECOMMITTED_OLD_RANDOMNESS_IDX, || self.old_randomness)?;
                region.assign_precommitted(|| "new_randomness", config.precommitted, PRECOMMITTED_NEW_RANDOMNESS_IDX, || self.new_randomness)?;

                config.balance_change.enable(&mut region, 5)?;
                region.assign_precommitted_from_instance(
                    || "load flag",
                    config.instance,
                    0,
                    config.precommitted,
                    PRECOMMITTED_FLAG_IDX,
                )?;
                region.assign_precommitted(|| "old_balance", config.precommitted, PRECOMMITTED_OLD_BALANCE_IDX, || self.old_balance)?;
                region.assign_precommitted(|| "amount", config.precommitted, PRECOMMITTED_AMOUNT_IDX, || self.amount)?;
                region.assign_precommitted(|| "new_balance", config.precommitted, PRECOMMITTED_NEW_BALANCE_IDX, || self.new_balance)
            },
        )?;

        // Apply range proof over new_balance
        let new_balance_rs = config.lookup_config.witness_check(
            layouter.namespace(|| "range_check_new_balance"),
            self.new_balance,
            self.num_words, // num_words parameter, so range proof covers [0, 2^{LIMB_BITS*num_words})
            true,
        )?;

        layouter.assign_region(
            || "commit new_balance range check",
            |mut region| {
                // let new_balance_cell_1 = new_balance_rs[0].copy_precommitted(
                //     || "new_balance_range_check",
                //     &mut region,
                //     config.precommitted,
                //     0,
                // )?;

                region.constrain_equal(new_balance_rs[0].cell(), new_balance_cell.cell())?;
                Ok(())
            },
        )?;

        Ok(())
    }
}

impl<F: PrimeFieldBits, Lookup: LookupRangeCheck<F, LIMB_BITS>, const LIMB_BITS: usize> Default
    for AffirmationWithBalanceChangeCircuit<F, Lookup, LIMB_BITS>
{
    fn default() -> Self {
        Self::new(
            4, // default num_words = 4
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::plonk::{keygen_vk, keygen_pk, create_proof_with_given_column_blindings, verify_proof, SingleVerifier, get_precommitted_col_comms};
    use halo2_proofs::poly::commitment::Params;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use pasta_curves::pallas;
    use rand_core::OsRng;
    use std::time::Instant;

    #[test]
    fn mock_affirmation_with_balance_change() {
        let mut rng = OsRng;

        let k = 7;
        const LIMB_BITS: usize = 6;
        let num_words = 8;

        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();
        
        let amount = pallas::Scalar::from(100u64);
        let old_balance = pallas::Scalar::from(500u64);
        let new_balance = old_balance + amount;

        // flag = 2 for when new_balance > old_balance, flag = 0 when new_balance < old_balance
        let flag = pallas::Scalar::from(2u64);
    
        assert_eq!(new_balance, old_balance + (flag - pallas::Scalar::ONE) * amount);

        let circuit = AffirmationWithBalanceChangeCircuit::<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            LIMB_BITS,
        >::new(
            num_words,
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount),
            Value::known(old_balance),
            Value::known(new_balance),
        );

        let prover = MockProver::run(k, &circuit, vec![vec![flag]]).unwrap();
        prover.assert_satisfied();

        // wrong flag value
        let wrong_flag = pallas::Scalar::from(0u64);
        let prover = MockProver::run(k, &circuit, vec![vec![wrong_flag]]).unwrap();
        assert!(prover.verify().is_err());

        // wrong new_balance
        let wrong_new_balance = old_balance + amount + pallas::Scalar::ONE;
        let circuit_wrong_balance = AffirmationWithBalanceChangeCircuit::<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            LIMB_BITS,
        >::new(
            num_words,
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount),
            Value::known(old_balance),
            Value::known(wrong_new_balance),
        );
        let prover = MockProver::run(k, &circuit_wrong_balance, vec![vec![flag]]).unwrap();
        assert!(prover.verify().is_err());

        // out-of-range new_balance
        let out_of_range_balance = pallas::Scalar::from(u64::MAX);
        let circuit_range_fail = AffirmationWithBalanceChangeCircuit::<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            LIMB_BITS,
        >::new(
            num_words,
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount),
            Value::known(old_balance),
            Value::known(out_of_range_balance),
        );
        let prover = MockProver::run(k, &circuit_range_fail, vec![vec![flag]]).unwrap();
        assert!(prover.verify().is_err());

        let amount = pallas::Scalar::from(200u64);
        let old_balance = pallas::Scalar::from(1000u64);
        let new_balance = old_balance - amount;
        let flag = pallas::Scalar::from(0u64);

        let circuit = AffirmationWithBalanceChangeCircuit::<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            LIMB_BITS,
        >::new(
            num_words,
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount),
            Value::known(old_balance),
            Value::known(new_balance),
        );

        let prover = MockProver::run(k, &circuit, vec![vec![flag]]).unwrap();
        prover.assert_satisfied();

        // wrong flag value
        let wrong_flag = pallas::Scalar::from(2u64);
        let prover = MockProver::run(k, &circuit, vec![vec![wrong_flag]]).unwrap();
        assert!(prover.verify().is_err());

    }

    #[test]
    fn real_affirmation_with_balance_change() {
        let mut rng = OsRng;

        let k = 7;
        const LIMB_BITS: usize = 6;
        let num_words = 8;

        // Set up the same witness values as in the mock test
        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();

        let amount = pallas::Scalar::from(100u64);
        let old_balance = pallas::Scalar::from(500u64);
        let new_balance = old_balance + amount;

        // flag = 2 for when new_balance > old_balance, flag = 0 when new_balance < old_balance
        let flag = pallas::Scalar::from(2u64);

        // Verify the balance equation
        assert_eq!(new_balance, old_balance + (flag - pallas::Scalar::ONE) * amount);

        // Create empty circuit for keygen (keygen requires a circuit that implements Default)
        let empty_circuit: AffirmationWithBalanceChangeCircuit<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            LIMB_BITS
        > = Default::default();

        // Set up parameters
        let params = Params::<pallas::Affine>::new(k);

        // Key generation
        let vk = keygen_vk(&params, &empty_circuit).unwrap();
        let pk = keygen_pk(&params, vk, &empty_circuit).unwrap();

        let start = Instant::now();

        // Create the actual circuit with witnesses
        let circuit = AffirmationWithBalanceChangeCircuit::<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            LIMB_BITS,
        >::new(
            num_words,
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount),
            Value::known(old_balance),
            Value::known(new_balance),
        );

        // Calculate number of blindings needed
        let num_blindings = pk.get_vk().blinding_factors() + 2;
        let blinding_rows = (0..num_blindings)
            .map(|_| pallas::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

        // Create proof
        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof_with_given_column_blindings(
            &params,
            &pk,
            &[circuit],
            &[&[&[flag]]],  // instance data contains the flag value
            vec![Some(vec![blinding_rows.clone()])],
            &mut rng,
            &mut transcript,
        )
        .unwrap();
        let proof = transcript.finalize();
        println!("Proving time: {:?}", start.elapsed());
        println!("Proof size: {} bytes", proof.len());

        let start = Instant::now();

        // Verify proof
        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        verify_proof(&params, pk.get_vk(), strategy, &[&[&[flag]]], &mut transcript).unwrap();
        println!("Verification time: {:?}", start.elapsed());

        // Verify commitment
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof.as_slice());
        let precommitted_commitments = get_precommitted_col_comms(1, pk.get_vk(), &mut transcript).unwrap();
        assert_eq!(precommitted_commitments[0].len(), 1); // Only 1 precommited column

        let domain = pk.get_vk().get_domain();

        let mut precommitted = domain.empty_lagrange();
        // Assign values based on the synthesize method layout
        precommitted[PRECOMMITTED_INITIAL_RHO_IDX] = initial_rho;
        precommitted[PRECOMMITTED_OLD_CURRENT_RHO_IDX] = old_current_rho;
        precommitted[PRECOMMITTED_NEW_CURRENT_RHO_IDX] = new_current_rho;
        precommitted[PRECOMMITTED_OLD_RANDOMNESS_IDX] = old_randomness;
        precommitted[PRECOMMITTED_NEW_RANDOMNESS_IDX] = new_randomness;
        precommitted[PRECOMMITTED_FLAG_IDX] = flag;
        precommitted[PRECOMMITTED_OLD_BALANCE_IDX] = old_balance;
        precommitted[PRECOMMITTED_AMOUNT_IDX] = amount;
        precommitted[PRECOMMITTED_NEW_BALANCE_IDX] = new_balance;

        let usable_rows = params.n as usize - (num_blindings - 1);
        for (i, v) in precommitted[usable_rows..].iter_mut().enumerate() {
            *v = blinding_rows[i];
        }
        let comm = params.commit_lagrange(&precommitted, (*blinding_rows.last().unwrap()).into()).into();
        assert_eq!(precommitted_commitments[0][0], comm);

        // Test with flag = 0 (balance decrease)
        let amount_decrease = pallas::Scalar::from(200u64);
        let old_balance_decrease = pallas::Scalar::from(1000u64);
        let new_balance_decrease = old_balance_decrease - amount_decrease;
        let flag_decrease = pallas::Scalar::from(0u64);

        let circuit_decrease = AffirmationWithBalanceChangeCircuit::<
            pallas::Scalar,
            LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>,
            LIMB_BITS,
        >::new(
            num_words,
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount_decrease),
            Value::known(old_balance_decrease),
            Value::known(new_balance_decrease),
        );

        let blinding_rows_decrease = (0..num_blindings)
            .map(|_| pallas::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof_with_given_column_blindings(
            &params,
            &pk,
            &[circuit_decrease],
            &[&[&[flag_decrease]]],
            vec![Some(vec![blinding_rows_decrease.clone()])],
            &mut rng,
            &mut transcript,
        )
        .unwrap();
        let proof_decrease = transcript.finalize();

        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof_decrease[..]);
        verify_proof(&params, pk.get_vk(), strategy, &[&[&[flag_decrease]]], &mut transcript).unwrap();
    }
}
