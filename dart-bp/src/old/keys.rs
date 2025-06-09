use ark_ec::short_weierstrass::Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ark_std::UniformRand;
use equality_across_groups::ec::commitments::SWPoint;
use rand::RngCore;

/*pub struct VerKey<PK: SWPoint>(pub Affine<PK>);
pub struct SigKey<PK: SWPoint>(pub PK::ScalarField);
pub struct EncKey<PK: SWPoint>(pub Affine<PK>);
pub struct DecKey<PK: SWPoint>(pub PK::ScalarField);

pub fn keygen_sig<R: RngCore, PK: SWPoint>(rng: &mut R, gen: Affine<PK>) -> (SigKey<PK>, VerKey<PK>) {
    let s = PK::ScalarField::rand(rng);
    let p = gen * s;
    (SigKey(s), VerKey(p.into_affine()))
}

// NOTE: Same as above but just in case we need to use a diff. scheme
pub fn keygen_enc<R: RngCore, PK: SWPoint>(rng: &mut R, gen: Affine<PK>) -> (DecKey<PK>, EncKey<PK>) {
    let s = PK::ScalarField::rand(rng);
    let p = gen * s;
    (DecKey(s), EncKey(p.into_affine()))
}*/

pub struct VerKey<PK: AffineRepr>(pub PK);
pub struct SigKey<PK: AffineRepr>(pub PK::ScalarField);
pub struct EncKey<PK: AffineRepr>(pub PK);
pub struct DecKey<PK: AffineRepr>(pub PK::ScalarField);

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
