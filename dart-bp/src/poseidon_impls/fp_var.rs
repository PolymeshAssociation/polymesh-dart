use ark_ff::{BitIteratorBE, Field, One, PrimeField, Zero};
use bulletproofs::r1cs::Variable;
use std::ops::Add;
use ark_relations::r1cs::SynthesisError;
use ark_r1cs_std::Assignment;
use std::ops::{Mul, MulAssign};


#[derive(Debug, Clone)]
#[must_use]
pub struct AllocatedFp<F: PrimeField> {
    pub(crate) value: Option<F>,
    /// The allocated variable corresponding to `self` in `self.cs`.
    pub variable: Variable<F>,
}

impl<F: PrimeField> AllocatedFp<F> {
    /// Constructs a new `AllocatedFp` from a (optional) value, a low-level
    /// Variable, and a `ConstraintSystemRef`.
    pub fn new(value: Option<F>, variable: Variable<F>) -> Self {
        Self {
            value,
            variable,
        }
    }
}

#[derive(Clone, Debug)]
#[must_use]
pub enum FpVar<F: PrimeField> {
    /// Represents a constant in the constraint system, which means that
    /// it does not have a corresponding variable.
    Constant(F),
    /// Represents an allocated variable constant in the constraint system.
    Var(AllocatedFp<F>),
}

// impl<F: PrimeField> FieldVar<F, F> for FpVar<F> {
impl<F: PrimeField> FpVar<F> {
    pub fn constant(f: F) -> Self {
        Self::Constant(f)
    }

    pub fn zero() -> Self {
        Self::Constant(F::zero())
    }

    pub fn one() -> Self {
        Self::Constant(F::one())
    }

    pub fn double(&self) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.double())),
            Self::Var(v) => Ok(Self::Var(v.double()?)),
        }
    }


    pub fn negate(&self) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(-*c)),
            Self::Var(v) => Ok(Self::Var(v.negate())),
        }
    }


    pub fn square(&self) -> Result<Self, SynthesisError> {
        match self {
            Self::Constant(c) => Ok(Self::Constant(c.square())),
            Self::Var(v) => Ok(Self::Var(v.square()?)),
        }
    }

    pub fn inverse(&self) -> Result<Self, SynthesisError> {
        match self {
            FpVar::Var(v) => v.inverse().map(FpVar::Var),
            FpVar::Constant(f) => f.inverse().get().map(FpVar::Constant),
        }
    }

    fn frobenius_map(&self, power: usize) -> Result<Self, SynthesisError> {
        match self {
            FpVar::Var(v) => v.frobenius_map(power).map(FpVar::Var),
            FpVar::Constant(f) => {
                let mut f = *f;
                f.frobenius_map_in_place(power);
                Ok(FpVar::Constant(f))
            },
        }
    }

    pub fn pow_by_constant<S: AsRef<[u64]>>(&self, exp: S) -> Result<Self, SynthesisError> {
        let mut res = Self::one();
        for i in BitIteratorBE::without_leading_zeros(exp) {
            res.square_in_place()?;
            if i {
                res *= self;
            }
        }
        Ok(res)
    }
}


impl<F: PrimeField> Add for FpVar<F> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        &self + &other
    }
}

impl<'a, F: PrimeField> Add<&'a FpVar<F>> for &'a FpVar<F> {
    type Output = FpVar<F>;

    fn add(self, other: &'a FpVar<F>) -> FpVar<F> {
        use FpVar::*;
        match (self, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 + *c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.add_constant(*c)),
            (Var(v1), Var(v2)) => Var(v1.add(v2)),
        }
    }
}

impl<'a, F: PrimeField> Add<F> for &'a FpVar<F> {
    type Output = FpVar<F>;

    fn add(self, other: F) -> FpVar<F> {
        self + &FpVar::Constant(other)
    }
}

impl<F: PrimeField> Mul for FpVar<F> {
    type Output = Self;

    fn mul(self, other: Self) -> Self::Output {
        &self * &other
    }
}

impl<'a, F: PrimeField> Mul<&'a FpVar<F>> for &'a FpVar<F> {
    type Output = FpVar<F>;

    fn mul(self, other: &'a FpVar<F>) -> FpVar<F> {
        use FpVar::*;
        match (self, other) {
            (Constant(c1), Constant(c2)) => Constant(*c1 * *c2),
            (Constant(c), Var(v)) | (Var(v), Constant(c)) => Var(v.mul_constant(*c)),
            (Var(v1), Var(v2)) => Var(v1.mul(v2)),
        }
    }
}

impl<'a, F: PrimeField> Mul<F> for &'a FpVar<F> {
    type Output = FpVar<F>;

    fn mul(self, other: F) -> FpVar<F> {
        if other.is_zero() {
            FpVar::Constant(F::zero())
        } else {
            self * &FpVar::Constant(other)
        }
    }
}

impl<F: PrimeField> MulAssign for FpVar<F> {
    fn mul_assign(&mut self, other: Self) {
        *self = self.clone() * other;
    }
}

impl<F: PrimeField> MulAssign<F> for FpVar<F> {
    fn mul_assign(&mut self, other: F) {
        *self = self.clone() * other;
    }
}

