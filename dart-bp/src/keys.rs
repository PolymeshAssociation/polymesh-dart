use ark_ec::{AffineRepr, CurveGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use rand::RngCore;

#[derive(Copy, Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq, Hash)]
pub struct VerKey<PK: AffineRepr>(pub PK);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SigKey<PK: AffineRepr>(pub PK::ScalarField);

#[derive(Copy, Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq, Hash)]
pub struct EncKey<PK: AffineRepr>(pub PK);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DecKey<PK: AffineRepr>(pub PK::ScalarField);

// NOTE that the generators used in both keys is same for now but will be made different soon.

pub fn keygen_sig<R: RngCore, PK: AffineRepr>(rng: &mut R, g: PK) -> (SigKey<PK>, VerKey<PK>) {
    let s = PK::ScalarField::rand(rng);
    let p = g * s;
    (SigKey(s), VerKey(p.into_affine()))
}

// NOTE: Same as above but just in case we need to use a diff. scheme
pub fn keygen_enc<R: RngCore, PK: AffineRepr>(rng: &mut R, g: PK) -> (DecKey<PK>, EncKey<PK>) {
    let s = PK::ScalarField::rand(rng);
    let p = g * s;
    (DecKey(s), EncKey(p.into_affine()))
}
