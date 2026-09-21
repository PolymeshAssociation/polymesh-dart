//! Batch trial decryption for Twisted ElGamal amount ciphertexts that share one decryption key.

#[allow(unused_imports)]
use crate::discrete_log::{solve_discrete_log_precomputed, solve_discrete_log_precomputed_batch};
use crate::{Error, error::Result};
use ark_ec::scalar_mul::glv::GLVConfig;
use ark_ec::scalar_mul::glv::eisenstein::glv_mul_same_scalar;
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_std::vec::Vec;
use zeroize::Zeroize;

/// `ct_i - sk^{-1} * eph_pk_i` for each amount ciphertext, sharing one `sk^{-1}` decomposition and
/// one field inversion per ladder column across the batch. `eph_pks` and `cts` must have equal
/// length. The plaintext point of amount `m` is `enc_gen * m`.
pub fn batch_decrypt_points<P: GLVConfig>(
    eph_pks: &[Affine<P>],
    cts: &[Affine<P>],
    sk: &P::ScalarField,
) -> Result<Vec<Affine<P>>> {
    if eph_pks.len() != cts.len() {
        return Err(Error::SizeMismatch(eph_pks.len().abs_diff(cts.len())));
    }
    let mut sk_inv = sk.inverse().ok_or(Error::InvertingZero)?;
    let masks = glv_mul_same_scalar::<P>(eph_pks, sk_inv);
    sk_inv.zeroize();
    let pts: Vec<Projective<P>> = cts.iter().zip(masks).map(|(ct, mask)| *ct - mask).collect();
    Ok(Projective::<P>::normalize_batch(&pts))
}

/// Batch-decrypt `n` amount ciphertexts under one `sk`: the shared-scalar GLV ladder for the point
/// step, then the precomputed baby-step/giant-step solver for each discrete log in `[0, max]`.
/// Returns the recovered amount per ciphertext, `None` where none exists in range.
pub fn batch_decrypt_amounts<P: GLVConfig>(
    eph_pks: &[Affine<P>],
    cts: &[Affine<P>],
    sk: &P::ScalarField,
    enc_gen: Affine<P>,
    max: u64,
) -> Result<Vec<Option<u64>>> {
    let pts = batch_decrypt_points::<P>(eph_pks, cts, sk)?;
    let base = enc_gen.into_group();
    // Ok(pts
    //     .iter()
    //     .map(|pt| solve_discrete_log_precomputed::<Projective<P>>(max, base, pt.into_group()))
    //     .collect())
    let targets = pts
        .iter()
        .map(|pt| pt.into_group())
        .collect::<Vec<Projective<P>>>();
    Ok(solve_discrete_log_precomputed_batch::<Projective<P>>(
        max, base, &targets,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_pallas::{Affine as PallasA, Fr as PallasScalar, PallasConfig};
    use ark_std::UniformRand;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;

    fn encrypt(
        enc_key_gen: PallasA,
        enc_gen: PallasA,
        pk: PallasA,
        m: u64,
        r: PallasScalar,
    ) -> (PallasA, PallasA) {
        let eph_pk = (pk.into_group() * r).into_affine();
        let ct = (enc_key_gen.into_group() * r + enc_gen.into_group() * PallasScalar::from(m))
            .into_affine();
        (eph_pk, ct)
    }

    #[test]
    fn batch_decrypt_points_works() {
        let mut rng = rand::thread_rng();
        let enc_key_gen = hash_to_pallas(b"batch-decrypt-points", b"g").into_affine();
        let enc_gen = hash_to_pallas(b"batch-decrypt-points", b"h").into_affine();

        let sk = PallasScalar::rand(&mut rng);
        let pk = (enc_key_gen.into_group() * sk).into_affine();

        let amounts = [0u64, 1, 42, 1000, u32::MAX as u64];
        let mut eph_pks = Vec::new();
        let mut cts = Vec::new();
        let mut expected = Vec::new();
        for &m in &amounts {
            let r = PallasScalar::rand(&mut rng);
            let (eph_pk, ct) = encrypt(enc_key_gen, enc_gen, pk, m, r);
            eph_pks.push(eph_pk);
            cts.push(ct);
            expected.push((enc_gen.into_group() * PallasScalar::from(m)).into_affine());
        }

        assert_eq!(
            batch_decrypt_points::<PallasConfig>(&eph_pks, &cts, &sk).unwrap(),
            expected
        );

        assert!(
            batch_decrypt_points::<PallasConfig>(&[], &[], &sk)
                .unwrap()
                .is_empty()
        );

        let err = batch_decrypt_points::<PallasConfig>(&eph_pks, &[cts[0]], &sk).unwrap_err();
        assert!(matches!(err, Error::SizeMismatch(4)));

        let err = batch_decrypt_points::<PallasConfig>(&eph_pks, &cts, &PallasScalar::from(0u64))
            .unwrap_err();
        assert!(matches!(err, Error::InvertingZero));
    }
}
