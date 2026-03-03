use codec::{Decode, Encode};
use scale_info::TypeInfo;

use polymesh_dart_bp::key_distribution;
use rand_core::{CryptoRng, RngCore};
use ark_ec::{AffineRepr};
use ark_std::UniformRand;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use crate::{PallasA, PallasScalar, WrappedCanonical};
use super::{dart_gens, CurveTreeParameters, AccountTreeConfig, EncryptionPublicKey, EncryptionSecretKey, Error};

/// Wraps [`key_distribution::KeyDistributionProof`], proving that a secret key has been
/// correctly split and encrypted under each recipient's public key.
///
/// The proof owner distributes their encryption secret key to `recipient_pks`
/// so each recipient can independently decrypt it.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct KeyDistributionProof {
    /// The public key corresponding to the distributed secret key (`enc_key_gen * sk`).
    pub public_key: EncryptionPublicKey,
    /// The recipient public keys the secret was distributed to.
    pub recipient_pks: Vec<EncryptionPublicKey>,
    inner: WrappedCanonical<key_distribution::KeyDistributionProof<PallasA>>,
}

impl KeyDistributionProof {
    /// Generate a key distribution proof proving that `enc_key` has been correctly
    /// split and encrypted for each entry in `recipient_pks`.
    ///
    /// `sk` is the key being distributed. `pk = enc_key_gen * sk`.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        sk: EncryptionSecretKey,
        pk_enc: &EncryptionPublicKey,
        recipient_pks: &[EncryptionPublicKey],
        nonce: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
    ) -> Result<Self, Error> {
        let pk = pk_enc.get_affine()?;
        let rec_pks: Vec<PallasA> = recipient_pks
            .iter()
            .map(|k| k.get_affine())
            .collect::<Result<_, _>>()?;

        let gens = dart_gens();
        let proof = key_distribution::KeyDistributionProof::new(
            rng,
            sk.inner().0,
            pk,
            &rec_pks,
            gens.enc_key_gen(),
            gens.leg_asset_value_gen(),
            nonce,
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
        )?;

        Ok(Self {
            public_key: pk_enc.clone(),
            recipient_pks: recipient_pks.to_vec(),
            inner: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        nonce: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let proof = self.inner.decode()?;
        let pk = self.public_key.get_affine()?;
        let rec_pks: Vec<PallasA> = self.recipient_pks
            .iter()
            .map(|k| k.get_affine())
            .collect::<Result<_, _>>()?;

        let gens = dart_gens();

        let mut rmc = RandomizedMultChecker::new(PallasScalar::rand(rng));

        proof.verify(
            rng,
            &pk,
            &rec_pks,
            gens.enc_key_gen(),
            gens.leg_asset_value_gen(),
            nonce,
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
            Some(&mut rmc),
        )?;
        Ok(())
    }

    /// Decrypt the distributed secret key as the recipient at `recipient_index`.
    ///
    /// The caller provides their own `recipient_key` whose public key must match
    /// `self.recipient_pks[recipient_index]`.
    pub fn decrypt(
        &self,
        recipient_index: usize,
        recipient_key: &EncryptionSecretKey,
    ) -> Result<PallasScalar, Error> {
        let proof = self.inner.decode()?;
        let sk_enc_inv = &recipient_key.inner().0;
        let enc_gen = dart_gens().leg_asset_value_gen().into_group();
        Ok(proof.decrypt(recipient_index, sk_enc_inv, enc_gen)?)
    }
}