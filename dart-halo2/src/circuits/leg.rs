use core::marker::PhantomData;
use ct_halo2::ec_chip::{assign_rerand_given_instance, configure_ecc, Ec};
use ct_halo2::multi_layer::{MultiLayerChip, MultiLayerConfig, SingleLayerWitness};
use ct_halo2::on_curve::{OnCurveChip, OnCurveConfig};
use ff::PrimeField;
use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheck;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Instance, Precommitted, Selector, TableColumn};
use halo2_proofs::poly::Rotation;
use crate::AffineSerializable;

#[derive(Clone, Debug)]
pub struct LegCreationEvenLayerCircuit<
    P: AffineSerializable,
    E: Ec<Base = P::Base, Scalar = P::ScalarExt>,
    const ARITY: usize,
    const NUM_KEYS_PLUS_1: usize,
> {
    pub x: [Value<P::Base>; NUM_KEYS_PLUS_1],
    pub y: [Value<P::Base>; NUM_KEYS_PLUS_1],
    pub blindings: [Value<P::Scalar>; NUM_KEYS_PLUS_1],
    pub tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
}

#[derive(Clone, Debug)]
pub struct LegCreationOddLayerCircuit<
    P: AffineSerializable,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    Lookup: LookupRangeCheck<P::Scalar, LIMB_BITS>,
    const LIMB_BITS: usize,
    const ARITY: usize,
> {
    num_words: usize,
    pub r1: Value<P::Scalar>,
    pub r2: Value<P::Scalar>,
    pub r3: Value<P::Scalar>,
    pub r4: Value<P::Scalar>,
    pub r2_r1_inv: Value<P::Scalar>,
    pub r3_r1_inv: Value<P::Scalar>,
    pub r4_r1_inv: Value<P::Scalar>,
    pub amount: Value<P::Scalar>,
    pub tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
    _marker: PhantomData<Lookup>,
}

impl<
    P: AffineSerializable,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    Lookup: LookupRangeCheck<P::Scalar, LIMB_BITS>,
    const LIMB_BITS: usize,
    const ARITY: usize
> LegCreationOddLayerCircuit<P, E, Lookup, LIMB_BITS, ARITY> {
    pub fn new(
        num_words: usize,
        r1: Value<P::Scalar>,
        r2: Value<P::Scalar>,
        r3: Value<P::Scalar>,
        r4: Value<P::Scalar>,
        r2_r1_inv: Value<P::Scalar>,
        r3_r1_inv: Value<P::Scalar>,
        r4_r1_inv: Value<P::Scalar>,
        amount: Value<P::Scalar>,
        tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
    ) -> Self {
        Self {
            num_words,
            r1,
            r2,
            r3,
            r4,
            r2_r1_inv,
            r3_r1_inv,
            r4_r1_inv,
            amount,
            tree_witness,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct LegCreationOddLayerConfig<
    E: Ec,
    Lookup: LookupRangeCheck<E::Base, LIMB_BITS> + Clone,
    const LIMB_BITS: usize,
> {
    pub precommitted: Column<Precommitted>,
    pub product_inv: Selector,
    pub lookup_config: Lookup,
    pub table_idx: TableColumn,
    pub ct_config: MultiLayerConfig<E>,
}

impl<
    F: PrimeField,
    P: AffineSerializable<ScalarExt = F>,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    Lookup: LookupRangeCheck<F, LIMB_BITS> + Clone,
    const LIMB_BITS: usize,
    const ARITY: usize
> Circuit<F> for LegCreationOddLayerCircuit<P, E, Lookup, LIMB_BITS, ARITY> {
    type Config = LegCreationOddLayerConfig<E, Lookup, LIMB_BITS>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        // TODO: Implement for V1
        todo!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let precommitted = meta.precommitted_column();
        let product_inv = meta.selector();

        meta.create_gate("product == r_i", |meta| {
            let s = meta.query_selector(product_inv);
            let r1 = meta.query_precommitted(precommitted, Rotation(0));
            let r2 = meta.query_precommitted(precommitted, Rotation(1));
            let r3 = meta.query_precommitted(precommitted, Rotation(2));
            let r4 = meta.query_precommitted(precommitted, Rotation(3));
            let r2_r1_inv = meta.query_precommitted(precommitted, Rotation(4));
            let r3_r1_inv = meta.query_precommitted(precommitted, Rotation(5));
            let r4_r1_inv = meta.query_precommitted(precommitted, Rotation(6));
            vec![s.clone() * (r2 - (r1.clone() * r2_r1_inv)), s.clone() * (r3 - (r1.clone() * r3_r1_inv)), s * (r4 - (r1 * r4_r1_inv))]
        });

        let running_sum = meta.advice_column();
        let table_idx = meta.lookup_table_column();
        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        let lookup_config = Lookup::configure(meta, running_sum, table_idx);

        let ct_config = MultiLayerChip::<E, ARITY>::configure(meta);

        Self::Config {
            precommitted,
            product_inv,
            lookup_config,
            table_idx,
            ct_config
        }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
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

        let amount_cell = layouter.assign_region(
            || "assign amount and r_i",
            |mut region| {
                config.product_inv.enable(&mut region, 0)?;
                region.assign_precommitted(|| "r1", config.precommitted, 0, || self.r1)?;
                region.assign_precommitted(|| "r2", config.precommitted, 1, || self.r2)?;
                region.assign_precommitted(|| "r3", config.precommitted, 2, || self.r3)?;
                region.assign_precommitted(|| "r4", config.precommitted, 3, || self.r4)?;
                region.assign_precommitted(|| "r2/r1", config.precommitted, 4, || self.r2_r1_inv)?;
                region.assign_precommitted(|| "r3/r1", config.precommitted, 5, || self.r3_r1_inv)?;
                region.assign_precommitted(|| "r4/r1", config.precommitted, 6, || self.r4_r1_inv)?;
                region.assign_precommitted(|| "amount", config.precommitted, 7, || self.amount)
            }
        )?;

        // Apply range proof over amount
        let amount_rs = config.lookup_config.witness_check(
            layouter.namespace(|| "range check amount"),
            self.amount,
            self.num_words, // num_words parameter, so range proof covers [0, 2^{LIMB_BITS*num_words})
            true,
        )?;

        layouter.assign_region(
            || "constraint amount",
            |mut region| {
                region.constrain_equal(amount_rs[0].cell(), amount_cell.cell())?;
                Ok(())
            },
        )?;

        let multi_layer_chip = MultiLayerChip::construct(config.ct_config);
        multi_layer_chip.assign_layers(
            layouter.namespace(|| "ct"),
            &self.tree_witness,
        )?;

        Ok(())
    }
}

#[derive(Clone)]
pub struct LegCreationEvenLayerConfig<E: Ec, > {
    pub x: Column<Advice>,
    pub y: Column<Advice>,
    pub on_curve: OnCurveConfig<E::Base>,
    pub ecc_config: E::EccConfig,
    pub instance: Column<Instance>,
    pub ct_config: MultiLayerConfig<E>,
}

impl<
    P: AffineSerializable,
    E: Ec<Base = P::Base, Scalar = P::ScalarExt>,
    const ARITY: usize,
    const NUM_KEYS_PLUS_1: usize,
> LegCreationEvenLayerCircuit<P, E, ARITY, NUM_KEYS_PLUS_1> {
    pub fn new(
        x: [Value<P::Base>; NUM_KEYS_PLUS_1],
        y: [Value<P::Base>; NUM_KEYS_PLUS_1],
        blindings: [Value<P::Scalar>; NUM_KEYS_PLUS_1],
        tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
    ) -> Self {
        Self {
            x,
            y,
            blindings,
            tree_witness
        }
    }
}

impl<
    F: PrimeField,
    P: AffineSerializable<Base = F>,
    E: Ec<Base = P::Base, Scalar = P::ScalarExt>,
    const ARITY: usize,
    const NUM_KEYS_PLUS_1: usize,
> Circuit<F> for LegCreationEvenLayerCircuit<P, E, ARITY, NUM_KEYS_PLUS_1> {
    type Config = LegCreationEvenLayerConfig<E>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        // TODO: Implement for V1
        todo!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // These could be 1 column but OnCurveChip::configure needs 2 columns. Maybe create a new abstration
        let col_x = meta.advice_column();
        let col_y = meta.advice_column();

        let sel_on_curve = meta.selector();

        let on_curve_config = OnCurveChip::configure(meta, col_x, col_y, sel_on_curve);

        let (ecc_config, instance) = configure_ecc::<E>(meta);

        let ct_config = MultiLayerChip::<E, ARITY>::configure(meta);

        Self::Config {
            x: col_x,
            y: col_y,
            on_curve: on_curve_config,
            ecc_config,
            ct_config,
            instance
        }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let on_curve_chip = OnCurveChip::construct(config.on_curve);
        let ecc_chip = E::construct(config.ecc_config.clone());
        let mut cells = vec![];
        for i in 0..NUM_KEYS_PLUS_1 {
            let (x_cell_curve, y_cell_curve) = on_curve_chip.assign(layouter.namespace(|| "on-curve"), &self.x[i], &self.y[i])?;
            let (x_cell_rerand, y_cell_rerand) = assign_rerand_given_instance::<E>(layouter.namespace(|| "rerand"), ecc_chip.clone(), self.blindings[i], self.x[i], self.y[i], 2*i + 0, 2*i + 1, config.instance);
            cells.push((x_cell_curve, y_cell_curve, x_cell_rerand, y_cell_rerand));
        }

        layouter.assign_region(
            || "constrain x, y",
            |mut region| {
                for (x_cell_curve, y_cell_curve, x_cell_rerand, y_cell_rerand) in &cells {
                    region.constrain_equal(x_cell_rerand.cell(), x_cell_curve.cell())?;
                    region.constrain_equal(y_cell_rerand.cell(), y_cell_curve.cell())?;
                }
                Ok(())
            })?;

        let multi_layer_chip = MultiLayerChip::construct(config.ct_config);
        multi_layer_chip.assign_layers(
            layouter.namespace(|| "ct"),
            &self.tree_witness,
        )?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::time::Instant;
    use ct_halo2::ec_chip::{PallasEc, VestaEc};
    use ct_halo2::fixed_points_pallas::{FixedPointsPallas, FullWidthPallas};
    use ct_halo2::fixed_points_vesta::{FixedPointsVesta, FullWidthVesta};
    use ct_halo2::tree::params::{CTCircuitParams, CTProvingKey, CTVerifyingKey};
    use ct_halo2::tree::sel_re_rand::{SelRerandParameters, SelRerandProvingParams, SelRerandVerifyingParams};
    use ff::Field;
    use group::{Curve, Group};
    use halo2_gadgets::ecc::chip::FixedPoint;
    use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::plonk::{keygen_vk, keygen_pk, create_proof_with_given_column_blindings, create_proof, get_the_only_precommitted_col_comm};
    use halo2_proofs::poly::commitment::Params;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use lazy_static::lazy_static;
    use pasta_curves::{pallas, vesta};
    use rand_core::OsRng;
    use crate::circuits::mint::tests::{BlindingGenParams, PALLAS_BLINDING_PARAMS};

    type PallasAffine = pallas::Affine;
    type VestaAffine = vesta::Affine;

    /// For tree with leaf in Vesta curve
    pub type VestaLeafBlindingGen = BlindingGenParams<VestaAffine, PallasAffine, FixedPointsVesta, FixedPointsPallas>;

    lazy_static! {
        pub static ref VESTA_BLINDING_PARAMS: VestaLeafBlindingGen = VestaLeafBlindingGen {
            blinding_gen_even: FullWidthPallas::generator(&FullWidthPallas),
            blinding_gen_odd: FullWidthVesta::generator(&FullWidthVesta),
            blinding_gen_tables_even: FixedPointsPallas,
            blinding_gen_tables_odd: FixedPointsVesta,
        };
    }

    // TODO: Remove hardcoding
    const LIMB_BITS: usize = 6;
    const NUM_WORDS: usize = 8;

    pub fn setup_curve_tree_params_for_leg_creation<const L: usize, const NUM_KEYS_PLUS_1: usize>(
        k: u32,
        height: u8,
    ) -> (
        CTCircuitParams<VestaAffine, PallasAffine>,
        CTProvingKey<VestaAffine, PallasAffine>,
        CTVerifyingKey<VestaAffine, PallasAffine>,
    ) {
        let params_odd = Params::<VestaAffine>::new(k);
        let params_even = Params::<PallasAffine>::new(k);

        let empty_even = SingleLayerWitness::<VestaEc, L>::default();
        let empty_odd = SingleLayerWitness::<PallasEc, L>::default();

        let mut empty_odd_layer_witnesses = vec![];
        let mut empty_even_layer_witnesses = vec![];

        for i in 0..height {
            if i % 2 == 0 {
                empty_even_layer_witnesses.push(empty_even.clone());
            } else {
                empty_odd_layer_witnesses.push(empty_odd.clone());
            }
        }

        let empty_odd_circuit = LegCreationEvenLayerCircuit::<PallasAffine, PallasEc, L, NUM_KEYS_PLUS_1> {
            x: [Value::unknown(); NUM_KEYS_PLUS_1],
            y: [Value::unknown(); NUM_KEYS_PLUS_1],
            blindings: [Value::unknown(); NUM_KEYS_PLUS_1],
            tree_witness: empty_odd_layer_witnesses
        };

        let empty_even_circuit = LegCreationOddLayerCircuit::<PallasAffine, VestaEc, LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>, LIMB_BITS, L>::new(
            NUM_WORDS,
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            empty_even_layer_witnesses,
        );

        let vk_odd = keygen_vk(&params_odd, &empty_odd_circuit).unwrap();
        let pk_odd = keygen_pk(&params_odd, vk_odd.clone(), &empty_odd_circuit).unwrap();

        let vk_even = keygen_vk(&params_even, &empty_even_circuit).unwrap();
        let pk_even = keygen_pk(&params_even, vk_even.clone(), &empty_even_circuit).unwrap();

        let circuit_params = CTCircuitParams {
            even: params_odd,
            odd: params_even
        };

        let ct_pk = CTProvingKey {
            even: pk_odd,
            odd: pk_even,
        };

        let ct_vk = CTVerifyingKey {
            even: vk_odd,
            odd: vk_even,
        };

        (circuit_params, ct_pk, ct_vk)
    }

    /// Generate SelRerand parameters using VESTA_BLINDING_PARAMS
    pub fn generate_vesta_sel_rerand_params<const L: usize>() -> (
        SelRerandParameters<VestaAffine, PallasAffine, FixedPointsVesta, FixedPointsPallas>,
        SelRerandProvingParams<VestaAffine, PallasAffine>,
        SelRerandVerifyingParams<VestaAffine, PallasAffine>
    ) {
        let blinding_gen_even = VESTA_BLINDING_PARAMS.blinding_gen_even;
        let blinding_gen_odd = VESTA_BLINDING_PARAMS.blinding_gen_odd;

        let sr_params = SelRerandParameters::<VestaAffine, PallasAffine, _, _>::new(
            1,
            L,
            b"test",
            blinding_gen_even,
            blinding_gen_odd,
            VESTA_BLINDING_PARAMS.blinding_gen_tables_even.clone(),
            VESTA_BLINDING_PARAMS.blinding_gen_tables_odd.clone(),
        );

        let sr_proving_params = sr_params.proving_params();
        let sr_verifying_params = sr_params.verifying_params();

        (sr_params, sr_proving_params, sr_verifying_params)
    }
    
    #[test]
    fn leg_creation() {
        let mut rng = OsRng;

        let k = 11;
        const L: usize = 1024;
        let height = 2;
        let num_leaves = 1 << height;
    }
}