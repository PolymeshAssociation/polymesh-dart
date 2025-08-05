use ark_ff::{Field};
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Variable};
use bulletproofs::r1cs::linear_combination::AllocatedScalar;
use bulletproofs::errors::R1CSError;
use std::marker::PhantomData;

/// Return result of Matrix x vect
pub fn mat_vec_mul<F: Field>(mat: &[Vec<F>], vect: &[F]) -> Vec<F> {
    let width = mat.len();
    debug_assert!(width == vect.len());
    let mut out = vec![F::zero(); width];
    for row in 0..width {
        for (col, inp) in vect.iter().enumerate() {
            out[row] += mat[row][col] * inp;
        }
    }
    out
}

/// Put result of Matrix x vect into vect and temp is a reusable temporary space to save allocations
pub fn mat_mut_vec_mul<F: Field>(mat: &[Vec<F>], vect: &mut [F], temp: &mut [F]) {
    temp.fill(F::zero());
    let width = mat.len();
    debug_assert!(width == vect.len());
    for row in 0..width {
        for (col, inp) in vect.iter().enumerate() {
            temp[row] += mat[row][col] * inp;
        }
    }
    vect.copy_from_slice(temp);
}

pub fn mat_mat_mul<F: Field>(mat1: &[Vec<F>], mat2: &[Vec<F>]) -> Vec<Vec<F>> {
    let t = mat1.len();
    let mut out = vec![vec![F::zero(); t]; t];
    for row in 0..t {
        for col1 in 0..t {
            for (col2, m2) in mat2.iter().enumerate() {
                out[row][col1] += mat1[row][col2] * m2[col1];
            }
        }
    }
    out
}

// gaussian elimination
pub fn mat_inverse<F: Field>(mat: &[Vec<F>]) -> Vec<Vec<F>> {
    let n = mat.len();
    assert!(mat[0].len() == n);

    let mut m = mat.to_owned();
    let mut inv = vec![vec![F::zero(); n]; n];
    for (i, invi) in inv.iter_mut().enumerate() {
        invi[i] = F::one();
    }

    // upper triangle
    for row in 0..n {
        for j in 0..row {
            // subtract from these rows
            let el = m[row][j];
            for col in 0..n {
                // do subtraction for each col
                if col < j {
                    m[row][col] = F::zero();
                } else {
                    let tmp = m[j][col] * el;
                    m[row][col] -= tmp;
                }
                if col > row {
                    inv[row][col] = F::zero();
                } else {
                    let tmp = inv[j][col] * el;
                    inv[row][col] -= tmp;
                }
            }
        }
        // make 1 in diag
        let el_inv = m[row][row].inverse().unwrap();
        for col in 0..n {
            match col.cmp(&row) {
                std::cmp::Ordering::Less => inv[row][col] *= el_inv,
                std::cmp::Ordering::Equal => {
                    m[row][col] = F::one();
                    inv[row][col] *= el_inv
                }
                std::cmp::Ordering::Greater => inv[row][col] *= el_inv,
            }
        }
    }

    // upper triangle
    for row in (0..n).rev() {
        for j in (row + 1..n).rev() {
            // subtract from these rows
            let el = m[row][j];
            for col in 0..n {
                // do subtraction for each col

                #[cfg(debug_assertions)]
                {
                    if col >= j {
                        m[row][col] = F::zero();
                    }
                }
                let tmp = inv[j][col] * el;
                inv[row][col] -= tmp;
            }
        }
    }

    #[cfg(debug_assertions)]
    {
        for (row, mrow) in m.iter().enumerate() {
            for (col, v) in mrow.iter().enumerate() {
                if row == col {
                    debug_assert!(*v == F::one());
                } else {
                    debug_assert!(*v == F::zero());
                }
            }
        }
    }

    inv
}

pub fn mat_transpose<F: Field>(mat: &[Vec<F>]) -> Vec<Vec<F>> {
    let rows = mat.len();
    let cols = mat[0].len();
    let mut transpose = vec![vec![F::zero(); rows]; cols];

    for (row, matrow) in mat.iter().enumerate() {
        for col in 0..cols {
            transpose[col][row] = matrow[col];
        }
    }
    transpose
}

/// Enforces that x is 0. Takes x and the inverse of x.
pub fn is_nonzero_gadget<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    x: AllocatedScalar<F>,
    x_inv: AllocatedScalar<F>,
) -> Result<(), R1CSError> {
    let x_lc = LinearCombination::from(x.variable);
    let y_lc = LinearCombination::from(F::one());
    let one_minus_y_lc = LinearCombination::from(Variable::One(PhantomData)) - y_lc.clone();

    // x * (1-y) = 0
    let (_, _, o1) = cs.multiply(x_lc.clone(), one_minus_y_lc);
    cs.constrain(o1.into());

    // x * x_inv = y
    let inv_lc: LinearCombination<F> = vec![(x_inv.variable, F::one())].iter().collect();
    let (_, _, o2) = cs.multiply(x_lc.clone(), inv_lc.clone());
    // Output wire should have value `y`
    cs.constrain(o2 - y_lc);

    Ok(())
}