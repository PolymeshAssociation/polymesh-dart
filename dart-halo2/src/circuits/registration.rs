// TODO: Check is this is any better https://github.com/axiom-crypto/halo2-lib/blob/main/halo2-base/src/gates/range/mod.rs

use core::marker::PhantomData;
use ff::{PrimeField, PrimeFieldBits};
use halo2_gadgets::poseidon::{Hash, Pow5Chip, Pow5Config};
use halo2_gadgets::utilities::lookup_range_check::{LookupRangeCheck, RunningSum};
use halo2_poseidon::{ConstantLength, P128Pow5T3, Spec};
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::circuit::floor_planner::V1;
use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Precommitted, Selector, TableColumn};
use halo2_proofs::poly::Rotation;

// Precommitted column indices for registration circuit
pub const PRECOMMITTED_SK_IDX: usize = 1;
pub const PRECOMMITTED_RHO_IDX: usize = 2;
pub const PRECOMMITTED_RHO_SQ_IDX: usize = 3;
pub const PRECOMMITTED_CHUNKS_START_IDX: usize = 4;

#[derive(Clone, Copy, Debug)]
pub struct AccountRegWithEncCircuit<
    F: PrimeFieldBits,
    Lookup: LookupRangeCheck<F, LIMB_BITS>,
    const NUM_CHUNKS: usize,
    const LIMB_BITS: usize,
> {
    sk: Value<F>,
    rho: Value<F>,
    rho_sq: Value<F>,
    num_words: usize,
    chunks: [Value<F>; NUM_CHUNKS],
    _marker: PhantomData<Lookup>,
}

impl<
    F: PrimeFieldBits,
    Lookup: LookupRangeCheck<F, LIMB_BITS>,
    const NUM_CHUNKS: usize,
    const LIMB_BITS: usize,
> AccountRegWithEncCircuit<F, Lookup, NUM_CHUNKS, LIMB_BITS>
{
    pub fn new(num_words: usize, sk: Value<F>, rho: Value<F>, rho_sq: Value<F>, chunks: [Value<F>; NUM_CHUNKS]) -> Self {
        AccountRegWithEncCircuit {
            sk,
            rho,
            rho_sq,
            num_words,
            chunks,
            _marker: PhantomData,
        }
    }

    pub fn new_default(num_words: usize) -> Self {
        Self::new(
            num_words,
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            [Value::unknown(); NUM_CHUNKS],
        )
    }
}

#[derive(Clone)]
pub struct AccountRegWithEncConfig<
    F: PrimeFieldBits,
    const LIMB_BITS: usize,
    Lookup: LookupRangeCheck<F, LIMB_BITS> + Clone,
> {
    pub hash_config: Pow5Config<F, 3, 2>,
    pub lookup_config: Lookup,
    pub table_idx: TableColumn,
    pub public: Column<Instance>,
    pub square: Selector,
    pub precommitted: Column<Precommitted>,
    phantom: PhantomData<F>,
}

impl<
    F: PrimeFieldBits,
    Lookup: LookupRangeCheck<F, LIMB_BITS> + Clone,
    const NUM_CHUNKS: usize,
    const LIMB_BITS: usize,
> Circuit<F> for AccountRegWithEncCircuit<F, Lookup, NUM_CHUNKS, LIMB_BITS>
where
    P128Pow5T3: Spec<F, 3, 2>,
{
    type Config = AccountRegWithEncConfig<F, LIMB_BITS, Lookup>;
    // NOTE: Changing the floor planner changes the indices in precommitted vector.
    type FloorPlanner = SimpleFloorPlanner;
    // type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        AccountRegWithEncCircuit::new(self.num_words, self.sk, self.rho, self.rho_sq, self.chunks)
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let state = [
            meta.advice_column(),
            meta.advice_column(),
            meta.advice_column(),
        ];
        let partial_sbox = meta.advice_column();
        let rc_a = [
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];
        let rc_b = [
            meta.fixed_column(),
            meta.fixed_column(),
            meta.fixed_column(),
        ];
        meta.enable_constant(rc_b[0]);
        let hash_config = Pow5Chip::configure::<P128Pow5T3>(meta, state, partial_sbox, rc_a, rc_b);

        // TODO: Reuse above? Have to carefully choose offset
        let public = meta.instance_column();
        meta.enable_equality(public);

        // TODO: Cant i reuse above columns
        let running_sum = meta.advice_column();
        let table_idx = meta.lookup_table_column();
        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        let lookup_config = Lookup::configure(meta, running_sum, table_idx);

        let precommitted = meta.precommitted_column();
        meta.enable_equality(precommitted);

        let square = meta.selector();
        meta.create_gate("square", |meta| {
            let s = meta.query_selector(square);
            let rho = meta.query_precommitted(precommitted, Rotation::cur());
            let rho_sq = meta.query_precommitted(precommitted, Rotation::next());
            // Enforce rho_sq = rho^2
            vec![s * (rho_sq - rho.square())]
        });

        Self::Config {
            hash_config,
            lookup_config,
            table_idx,
            public,
            square,
            precommitted,
            phantom: PhantomData,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = Pow5Chip::construct(config.hash_config.clone());

        let hasher = Hash::<_, _, P128Pow5T3, ConstantLength<2>, 3, 2>::init(
            chip,
            layouter.namespace(|| "poseidon"),
        )?;

        let preimage = layouter.assign_region(
            || "load sk and counter",
            |mut region| {
                let sk_cell = region.assign_advice(
                    || "load sk",
                    config.hash_config.state[0],
                    0,
                    || self.sk,
                )?;

                let cnt_cell = region.assign_advice_from_instance(
                    || "load counter",
                    config.public,
                    0,
                    config.hash_config.state[1],
                    0,
                )?;

                let s =
                    sk_cell.copy_precommitted(|| "sk-com", &mut region, config.precommitted, 0)?;
                // println!("s={:?}", s.cell());

                Ok([sk_cell, cnt_cell])
            },
        )?;

        let rho_cell = hasher.hash(layouter.namespace(|| "hash"), preimage)?;

        layouter.assign_region(
            || "constrain rho",
            |mut region| {
                // let expected_rho_cell = region.assign_advice(
                //     || "load rho",
                //     config.hash_config.state[0], // TODO: Is overriding safe?
                //     0,
                //     || self.rho,
                // )?;
                // let r = expected_rho_cell.copy_precommitted(
                //     || "rho-com",
                //     &mut region,
                //     config.precommitted,
                //     0,
                // )?;
                // println!("rho={:?}", r.cell());

                let expected_rho_cell = region.assign_precommitted(
                    || "rho-com",
                    config.precommitted,
                    0,
                    || self.rho,
                )?;
                region.constrain_equal(rho_cell.cell(), expected_rho_cell.cell())?;

                config.square.enable(&mut region, 0)?;
                region.assign_precommitted(|| "rho^2", config.precommitted, 1, || self.rho_sq)?;

                Ok(())
            },
        )?;

        // TODO: Cant i make it shared with other circuits?
        load::<F, LIMB_BITS>(config.table_idx, &mut layouter)?;

        let mut val_cells = Vec::with_capacity(NUM_CHUNKS);
        for val in self.chunks.iter() {
            let rs = config.lookup_config.witness_check(
                layouter.namespace(|| format!("Lookup {:?}", self.num_words)),
                *val,
                self.num_words,
                true,
            )?;
            val_cells.push(rs);
        }

        layouter.assign_region(
            || "commit chunks",
            |mut region| {
                for (i, val_cell) in val_cells.iter().enumerate() {
                    let c = val_cell[0].copy_precommitted(
                        || format!("chunk_{i}-com"),
                        &mut region,
                        config.precommitted,
                        i,
                    )?;
                    // println!("c_{i}={:?}", c.cell());
                }
                Ok(())
            },
        )?;

        Ok(())
    }
}

fn load<F: PrimeFieldBits, const LIMB_BITS: usize>(
    table_idx: TableColumn,
    layouter: &mut impl Layouter<F>,
) -> Result<(), Error> {
    layouter.assign_table(
        || "table_idx",
        |mut table| {
            for index in 0..(1 << LIMB_BITS) {
                table.assign_cell(
                    || "table_idx",
                    table_idx,
                    index,
                    || Value::known(F::from(index as u64)),
                )?;
            }
            Ok(())
        },
    )
}

#[derive(Clone, Copy, Debug)]
pub struct AccountRegCircuit<F: PrimeField> {
    sk: Value<F>,
    rho: Value<F>,
    rho_sq: Value<F>,
}

impl<F: PrimeField> AccountRegCircuit<F> {
    pub fn new(sk: Value<F>, rho: Value<F>, rho_sq: Value<F>) -> Self {
        AccountRegCircuit { sk, rho, rho_sq }
    }
}

impl<F: PrimeField> Default for AccountRegCircuit<F> {
    fn default() -> Self {
        Self::new(Value::unknown(), Value::unknown(), Value::unknown())
    }
}

#[derive(Clone)]
pub struct AccountRegConfig<F: PrimeField> {
    pub hash_config: Pow5Config<F, 3, 2>,
    pub public: Column<Instance>,
    pub square: Selector,
    pub precommitted: Column<Precommitted>,
}

impl<F: PrimeField> Circuit<F> for AccountRegCircuit<F>
where
    P128Pow5T3: Spec<F, 3, 2>,
{
    type Config = AccountRegConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        AccountRegCircuit::new(self.sk, self.rho, self.rho_sq)
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let state = [meta.advice_column(), meta.advice_column(), meta.advice_column()];
        let partial_sbox = meta.advice_column();
        let rc_a = [meta.fixed_column(), meta.fixed_column(), meta.fixed_column()];
        let rc_b = [meta.fixed_column(), meta.fixed_column(), meta.fixed_column()];
        meta.enable_constant(rc_b[0]);
        let hash_config = Pow5Chip::configure::<P128Pow5T3>(meta, state, partial_sbox, rc_a, rc_b);

        let public = meta.instance_column();
        meta.enable_equality(public);

        let precommitted = meta.precommitted_column();
        meta.enable_equality(precommitted);

        let square = meta.selector();
        meta.create_gate("square", |meta| {
            let s = meta.query_selector(square);
            let rho = meta.query_precommitted(precommitted, Rotation::cur());
            let rho_sq = meta.query_precommitted(precommitted, Rotation::next());
            // Enforce rho_sq = rho^2
            vec![s * (rho_sq - rho.square())]
        });

        AccountRegConfig {
            hash_config,
            public,
            square,
            precommitted,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = Pow5Chip::construct(config.hash_config.clone());
        let hasher = Hash::<_, _, P128Pow5T3, ConstantLength<2>, 3, 2>::init(
            chip,
            layouter.namespace(|| "poseidon"),
        )?;

        let preimage = layouter.assign_region(
            || "load sk and counter",
            |mut region| {
                let sk_cell = region.assign_advice(
                    || "load sk",
                    config.hash_config.state[0],
                    0,
                    || self.sk,
                )?;
                let cnt_cell = region.assign_advice_from_instance(
                    || "load counter",
                    config.public,
                    0,
                    config.hash_config.state[1],
                    0,
                )?;
                let s = sk_cell.copy_precommitted(|| "sk-com", &mut region, config.precommitted, 0)?;
                // println!("s={:?}", s.cell());
                Ok([sk_cell, cnt_cell])
            },
        )?;

        let rho_cell = hasher.hash(layouter.namespace(|| "hash"), preimage)?;

        layouter.assign_region(
            || "constrain rho",
            |mut region| {
                // let expected_rho_cell = region.assign_advice(
                //     || "load rho",
                //     config.hash_config.state[0],
                //     0,
                //     || self.rho,
                // )?;
                // let r = expected_rho_cell.copy_precommitted(
                //     || "rho-com",
                //     &mut region,
                //     config.precommitted,
                //     0,
                // )?;
                // println!("rho={:?}", r.cell());

                let expected_rho_cell = region.assign_precommitted(
                    || "rho-com",
                    config.precommitted,
                    0,
                    || self.rho,
                )?;
                region.constrain_equal(rho_cell.cell(), expected_rho_cell.cell())?;

                config.square.enable(&mut region, 0)?;
                region.assign_precommitted(|| "rho^2", config.precommitted, 1, || self.rho_sq)?;

                Ok(())
            },
        )?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ff::Field;
    use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
    use halo2_proofs::dev::{CircuitCost, CircuitGates, MockProver};
    use halo2_proofs::plonk::{SingleVerifier, create_proof_with_given_column_blindings, keygen_pk, keygen_vk, verify_proof, get_the_only_precommitted_col_comm};
    use halo2_proofs::poly::commitment::Params;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use pasta_curves::{pallas::Scalar as Fr, pallas::Affine as PallasA, pallas};
    use rand_core::{OsRng, RngCore};
    use std::time::Instant;

    #[test]
    fn mock_reg_with_enc_circuit() {
        let k = 13;

        const NUM_CHUNKS: usize = 6;
        const LIMB_BITS: usize = 12;
        let num_words = 4;

        let mut rng = OsRng;

        let mut vals = [0; NUM_CHUNKS];
        for i in 0..NUM_CHUNKS {
            vals[i] = rng.next_u32();
        }

        let mut chunks = [Value::unknown(); NUM_CHUNKS];
        for i in 0..NUM_CHUNKS {
            chunks[i] = Value::known(Fr::from(vals[i] as u64));
        }

        let sk = Fr::random(&mut rng);
        let counter = Fr::from(100);
        let rho = halo2_poseidon::Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init()
            .hash([sk, counter]);
        let rho_sq = rho.square();

        let circuit = AccountRegWithEncCircuit::<
            Fr,
            LookupRangeCheckConfig<Fr, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >::new(num_words, Value::known(sk), Value::known(rho), Value::known(rho_sq), chunks);

        let prover = MockProver::run(k, &circuit, vec![vec![counter]]).unwrap();
        prover.assert_satisfied();

        println!("LIMB_BITS={LIMB_BITS}, num_words={num_words}, NUM_CHUNKS={NUM_CHUNKS}");
        let gates = CircuitGates::collect::<_, AccountRegWithEncCircuit<
            Fr,
            LookupRangeCheckConfig<Fr, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >>();
        println!("gates {}", gates);
        let cost = CircuitCost::<
            pallas::Point,
            AccountRegWithEncCircuit<
                Fr,
                LookupRangeCheckConfig<Fr, LIMB_BITS>,
                NUM_CHUNKS,
                LIMB_BITS,
            >
        >::measure(k, &circuit);
        println!("cost {:#?}", cost);
        let proof_size = cost.proof_size(1);
        println!("proof_size {:#?}", proof_size);

        // Wrong sk
        let circuit = AccountRegWithEncCircuit::<
            Fr,
            LookupRangeCheckConfig<Fr, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >::new(
            num_words,
            Value::known(Fr::random(&mut rng)),
            Value::known(rho),
            Value::known(rho_sq),
            chunks,
        );

        let prover = MockProver::run(k, &circuit, vec![vec![counter]]).unwrap();
        assert!(prover.verify().is_err());

        // Wrong counter
        let circuit = AccountRegWithEncCircuit::<
            Fr,
            LookupRangeCheckConfig<Fr, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >::new(num_words, Value::known(sk), Value::known(rho), Value::known(rho_sq), chunks);

        let prover =
            MockProver::run(k, &circuit, vec![vec![counter + Fr::ONE]]).unwrap();
        assert!(prover.verify().is_err());

        // Out of range chunks
        let mut chunks = [Value::unknown(); NUM_CHUNKS];
        for i in 0..NUM_CHUNKS {
            chunks[i] = Value::known(Fr::from(u64::MAX - i as u64));
        }

        let circuit = AccountRegWithEncCircuit::<
            Fr,
            LookupRangeCheckConfig<Fr, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >::new(num_words, Value::known(sk), Value::known(rho), Value::known(rho_sq), chunks);

        let prover = MockProver::run(k, &circuit, vec![vec![counter]]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn real_reg_with_enc_circuit() {
        let k = 7;
        const NUM_CHUNKS: usize = 6;
        const LIMB_BITS: usize = 6;
        let num_words = 8;

        let mut rng = OsRng;
        let mut vals = [0; NUM_CHUNKS];
        for i in 0..NUM_CHUNKS {
            vals[i] = rng.next_u32();
        }
        let mut chunks = [Value::unknown(); NUM_CHUNKS];
        for i in 0..NUM_CHUNKS {
            chunks[i] = Value::known(Fr::from(vals[i] as u64));
        }

        let sk = Fr::random(&mut rng);
        let counter = Fr::from(100);
        let rho = halo2_poseidon::Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init()
            .hash([sk, counter]);
        let rho_sq = rho.square();

        println!("LIMB_BITS={LIMB_BITS}, num_words={num_words}, NUM_CHUNKS={NUM_CHUNKS}");
        let start = Instant::now();
        let empty_circuit = AccountRegWithEncCircuit::<
            Fr,
            LookupRangeCheckConfig<Fr, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >::new_default(num_words);
        let params = Params::<PallasA>::new(k);
        let vk = keygen_vk(&params, &empty_circuit).unwrap();
        let pk = keygen_pk(&params, vk, &empty_circuit).unwrap();
        println!("Keygen time: {:?}", start.elapsed());

        let start = Instant::now();
        let circuit = AccountRegWithEncCircuit::<
            Fr,
            LookupRangeCheckConfig<Fr, LIMB_BITS>,
            NUM_CHUNKS,
            LIMB_BITS,
        >::new(num_words, Value::known(sk), Value::known(rho), Value::known(rho_sq), chunks);

        let num_blindings = pk.get_vk().blinding_factors() + 2;
        let blinding_rows = (0..num_blindings)
            .map(|_| Fr::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof_with_given_column_blindings(
            &params,
            &pk,
            &[circuit],
            &[&[&[counter]]],
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
        verify_proof(&params, pk.get_vk(), strategy, &[&[&[counter]]], &mut transcript).unwrap();
        println!("Verification time: {:?}", start.elapsed());

        // Verify commitment
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof.as_slice());
        let precommitted_commitment = get_the_only_precommitted_col_comm(pk.get_vk(), &mut transcript).unwrap();

        let domain = pk.get_vk().get_domain();
        
        let mut precommitted = domain.empty_lagrange();
        precommitted[PRECOMMITTED_SK_IDX] = sk;
        precommitted[PRECOMMITTED_RHO_IDX] = rho;
        precommitted[PRECOMMITTED_RHO_SQ_IDX] = rho_sq;
        for i in 0..NUM_CHUNKS {
            precommitted[PRECOMMITTED_CHUNKS_START_IDX + i] = Fr::from(vals[i] as u64);
        }
        let usable_rows = params.n as usize - (num_blindings - 1);
        for (i, v) in precommitted[usable_rows..].iter_mut().enumerate() {
            *v = blinding_rows[i];
        }
        let comm = params.commit_lagrange(&precommitted, (*blinding_rows.last().unwrap()).into()).into();
        assert_eq!(precommitted_commitment, comm);
    }

    #[test]
    fn mock_reg_circuit() {
        let k = 6;
        let mut rng = OsRng;
        let sk = Fr::random(&mut rng);
        let counter = Fr::from(100);
        let rho = halo2_poseidon::Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init()
            .hash([sk, counter]);
        let rho_sq = rho.square();

        let circuit = AccountRegCircuit::<Fr>::new(Value::known(sk), Value::known(rho), Value::known(rho_sq));
        let prover = MockProver::run(k, &circuit, vec![vec![counter]]).unwrap();
        prover.assert_satisfied();

        let gates = CircuitGates::collect::<_, AccountRegCircuit<Fr>>();
        println!("gates {}", gates);
        let cost = CircuitCost::<pallas::Point, AccountRegCircuit<Fr>>::measure(k, &circuit);
        println!("cost {:#?}", cost);
        let proof_size = cost.proof_size(1);
        println!("proof_size {:#?}", proof_size);

        // Wrong sk
        let circuit = AccountRegCircuit::<Fr>::new(Value::known(Fr::random(&mut rng)), Value::known(rho), Value::known(rho_sq));
        let prover = MockProver::run(k, &circuit, vec![vec![counter]]).unwrap();
        assert!(prover.verify().is_err());

        // Wrong counter
        let circuit = AccountRegCircuit::<Fr>::new(Value::known(sk), Value::known(rho), Value::known(rho_sq));
        let prover = MockProver::run(k, &circuit, vec![vec![counter + Fr::ONE]]).unwrap();
        assert!(prover.verify().is_err());

        // Wrong rho_sq
        let circuit = AccountRegCircuit::<Fr>::new(Value::known(sk), Value::known(rho), Value::known(rho_sq + Fr::ONE));
        let prover = MockProver::run(k, &circuit, vec![vec![counter]]).unwrap();
        assert!(prover.verify().is_err());
    }

    #[test]
    fn real_reg_circuit() {
        let k = 6;
        let mut rng = OsRng;
        let sk = Fr::random(&mut rng);
        let counter = Fr::from(100);
        let rho = halo2_poseidon::Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init()
            .hash([sk, counter]);

        let start = Instant::now();
        let empty_circuit = AccountRegCircuit::<Fr>::default();
        let params = Params::<PallasA>::new(k);
        let vk = keygen_vk(&params, &empty_circuit).unwrap();
        let pk = keygen_pk(&params, vk, &empty_circuit).unwrap();
        println!("Keygen time: {:?}", start.elapsed());

        let rho_sq = rho.square();

        let start = Instant::now();
        let circuit = AccountRegCircuit::<Fr>::new(Value::known(sk), Value::known(rho), Value::known(rho_sq));
        let num_blindings = pk.get_vk().blinding_factors() + 2;
        let blinding_rows = (0..num_blindings)
            .map(|_| Fr::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
        create_proof_with_given_column_blindings(
            &params,
            &pk,
            &[circuit],
            &[&[&[counter]]],
            vec![Some(vec![blinding_rows.clone()])],
            &mut rng,
            &mut transcript,
        ).unwrap();
        let proof = transcript.finalize();

        println!("Proving time: {:?}", start.elapsed());
        println!("Proof size: {} bytes", proof.len());

        let start = Instant::now();
        let strategy = SingleVerifier::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
        verify_proof(&params, pk.get_vk(), strategy, &[&[&[counter]]], &mut transcript).unwrap();
        println!("Verification time: {:?}", start.elapsed());

        // Verify commitment
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof.as_slice());
        let precommitted_commitment = get_the_only_precommitted_col_comm(pk.get_vk(), &mut transcript).unwrap();

        let domain = pk.get_vk().get_domain();

        let mut precommitted = domain.empty_lagrange();
        precommitted[PRECOMMITTED_SK_IDX] = sk;
        precommitted[PRECOMMITTED_RHO_IDX] = rho;
        precommitted[PRECOMMITTED_RHO_SQ_IDX] = rho_sq;
        let usable_rows = params.n as usize - (num_blindings - 1);
        for (i, v) in precommitted[usable_rows..].iter_mut().enumerate() {
            *v = blinding_rows[i];
        }
        let comm = params.commit_lagrange(&precommitted, (*blinding_rows.last().unwrap()).into()).into();
        assert_eq!(precommitted_commitment, comm);
    }
}
