use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::One;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, vec::Vec};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use crate::account::{TXN_CHALLENGE_LABEL, TXN_INSTANCE_LABEL};
use crate::error::{Result, Error};

#[derive(Copy, Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq, Hash)]
pub struct VerKey<PK: AffineRepr>(pub PK);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "testing", derive(CanonicalSerialize, CanonicalDeserialize))]
pub struct SigKey<PK: AffineRepr>(pub PK::ScalarField);

#[derive(Copy, Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq, Hash)]
pub struct EncKey<PK: AffineRepr>(pub PK);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "testing", derive(CanonicalSerialize, CanonicalDeserialize))]
pub struct DecKey<PK: AffineRepr>(pub PK::ScalarField);

pub fn keygen_sig<R: CryptoRngCore, PK: AffineRepr>(
    rng: &mut R,
    j: PK,
) -> (SigKey<PK>, VerKey<PK>) {
    let s = PK::ScalarField::rand(rng);
    let p = j * s;
    (SigKey(s), VerKey(p.into_affine()))
}

// NOTE: Same as above but just in case we need to use a diff. scheme
pub fn keygen_enc<R: CryptoRngCore, PK: AffineRepr>(
    rng: &mut R,
    g: PK,
) -> (DecKey<PK>, EncKey<PK>) {
    let s = PK::ScalarField::rand(rng);
    let p = g * s;
    (DecKey(s), EncKey(p.into_affine()))
}

const INVESTOR_KEY_REG_TXN_LABEL: &'static [u8; 25] = b"investor-key-registration";

const AUD_MED_KEY_REG_TXN_LABEL: &'static [u8; 33] = b"auditor/mediator-key-registration";

/// Register keys for 1 or more investors. For each investor, we have a signature and an encryption key.
/// Uses Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf)
pub struct InvestorKeyRegProof<G: AffineRepr> {
    pub sig: (G, G::ScalarField),
    pub enc: (G, G::ScalarField),
}

impl<G: AffineRepr> InvestorKeyRegProof<G> {
    /// Each item of `keys` is a pair where the first element is the pair of signing public
    /// and secret key and the second element is the pair of encryption public and secret key.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        keys: Vec<((G, G::ScalarField), (G, G::ScalarField))>,
        nonce: &[u8],
        sig_key_gen: G,
        enc_key_gen: G
    ) -> Result<Self> {
        // Note: This proof can be reduced to half in size if both sig and enc keys use the same generator

        let mut transcript = MerlinTranscript::new(INVESTOR_KEY_REG_TXN_LABEL);
        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        sig_key_gen.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        for ((s, _), (e, _)) in keys.iter() {
            s.serialize_compressed(&mut transcript)?;
            e.serialize_compressed(&mut transcript)?;
        }

        let r_sig = G::ScalarField::rand(rng);
        let r_enc = G::ScalarField::rand(rng);

        let t_sig = (sig_key_gen * r_sig).into_affine();
        let t_enc = (enc_key_gen * r_enc).into_affine();

        t_sig.serialize_compressed(&mut extra_instance)?;
        t_enc.serialize_compressed(&mut extra_instance)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut s_sig = r_sig;
        let mut s_enc = r_enc;

        let mut c = challenge;
        for ((_, s), (_, e)) in keys.into_iter() {
            s_sig += c * s;
            s_enc += c * e;
            c = c * challenge;
        }

        Ok(Self {sig: (t_sig, s_sig), enc: (t_enc, s_enc)})
    }

    /// Each item of `keys` is a pair where the first element is the signing public key and the
    /// second element is the encryption public key
    pub fn verify(
        &self,
        pub_keys: Vec<(G, G)>,
        nonce: &[u8],
        sig_key_gen: G,
        enc_key_gen: G
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(INVESTOR_KEY_REG_TXN_LABEL);
        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        sig_key_gen.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        for (s, e) in pub_keys.iter() {
            s.serialize_compressed(&mut transcript)?;
            e.serialize_compressed(&mut transcript)?;
        }

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut sig_keys = vec![];
        let mut enc_keys = vec![];
        let mut challenge_powers = vec![];
        let mut c = G::ScalarField::one();
        for (s, e) in pub_keys.into_iter() {
            sig_keys.push(s);
            enc_keys.push(e);
            c = c * challenge;
            challenge_powers.push(c);
        }

        // Even the following 2 checks can be combined into 1 with RLC

        if sig_key_gen * self.sig.1 != (self.sig.0 + G::Group::msm_unchecked(&sig_keys, &challenge_powers)) {
            return Err(Error::ProofVerificationError(
                "Signature key proof verification failed".to_string(),
            ));
        }

        if enc_key_gen * self.enc.1 != (self.enc.0 + G::Group::msm_unchecked(&enc_keys, &challenge_powers)) {
            return Err(Error::ProofVerificationError(
                "Encryption key proof verification failed".to_string(),
            ));
        }

        Ok(())
    }
}

/// Register keys for 1 or more auditor/mediator. For each auditor/mediator key, we have an encryption key.
/// Supporting registering multiple keys as an entity might use different keys for different assets and roles (like delegating in an org)
/// Uses Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf)
pub struct AudMedRegProof<G: AffineRepr> {
    pub t: G,
    pub s: G::ScalarField,
}

impl<G: AffineRepr> AudMedRegProof<G> {
    /// Each item of `keys` is a pair of encryption public and secret key.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        keys: Vec<(G, G::ScalarField)>,
        nonce: &[u8],
        enc_key_gen: G
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(AUD_MED_KEY_REG_TXN_LABEL);
        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        for (e, _) in keys.iter() {
            e.serialize_compressed(&mut transcript)?;
        }

        let r = G::ScalarField::rand(rng);
        let t = (enc_key_gen * r).into_affine();

        t.serialize_compressed(&mut extra_instance)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut s = r;
        let mut c = challenge;
        for (_, e) in keys.into_iter() {
            s += c * e;
            c = c * challenge;
        }

        Ok(Self { t, s })
    }

    pub fn verify(
        &self,
        pub_keys: Vec<G>,
        nonce: &[u8],
        enc_key_gen: G
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(AUD_MED_KEY_REG_TXN_LABEL);
        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance)?;
        enc_key_gen.serialize_compressed(&mut extra_instance)?;

        transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        for e in pub_keys.iter() {
            e.serialize_compressed(&mut transcript)?;
        }

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut enc_keys = vec![];
        let mut challenge_powers = vec![];
        let mut c = G::ScalarField::one();
        for e in pub_keys.into_iter() {
            enc_keys.push(e);
            c = c * challenge;
            challenge_powers.push(c);
        }

        if enc_key_gen * self.s != (self.t + G::Group::msm_unchecked(&enc_keys, &challenge_powers)) {
            return Err(Error::ProofVerificationError(
                "Encryption key proof verification failed".to_string(),
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::keys::{keygen_enc, keygen_sig};

    type PallasA = ark_pallas::Affine;

    #[test]
    fn investor_key_reg_proof() {
        let mut rng = rand::thread_rng();

        let num_investors = 5;

        let sig_key_gen = PallasA::rand(&mut rng);
        let enc_key_gen = PallasA::rand(&mut rng);

        let mut keypairs = Vec::with_capacity(num_investors);
        let mut pub_keys = Vec::with_capacity(num_investors);

        for _ in 0..num_investors {
            let (sig_sk, sig_pk) = keygen_sig(&mut rng, sig_key_gen);
            let (enc_sk, enc_pk) = keygen_enc(&mut rng, enc_key_gen);
            keypairs.push(((sig_pk.0, sig_sk.0), (enc_pk.0, enc_sk.0)));
            pub_keys.push((sig_pk.0, enc_pk.0));
        }

        let nonce = b"test-nonce";

        let proof = InvestorKeyRegProof::new(
            &mut rng,
            keypairs,
            nonce,
            sig_key_gen,
            enc_key_gen
        ).unwrap();

        proof.verify(
            pub_keys.clone(),
            nonce,
            sig_key_gen,
            enc_key_gen
        ).unwrap();

        // Fail when less keys are provided
        let fewer_public_keys = pub_keys[..3].to_vec();
        let result = proof.verify(
            fewer_public_keys,
            nonce,
            sig_key_gen,
            enc_key_gen
        );
        assert!(result.is_err());

        // Fail when wrong keys are provided
        let mut wrong_public_keys = pub_keys.clone();
        wrong_public_keys[0] = (PallasA::rand(&mut rng), PallasA::rand(&mut rng));
        let result = proof.verify(
            wrong_public_keys,
            nonce,
            sig_key_gen,
            enc_key_gen
        );
        assert!(result.is_err());

        // Fail when wrong generators are provided
        let result = proof.verify(
            pub_keys,
            nonce,
            enc_key_gen,
            sig_key_gen
        );
        assert!(result.is_err());
    }

    #[test]
    fn aud_med_key_reg_proof() {
        let mut rng = rand::thread_rng();

        let num_aud_med = 5;

        let enc_key_gen = PallasA::rand(&mut rng);

        let mut keypairs = Vec::with_capacity(num_aud_med);
        let mut pub_keys = Vec::with_capacity(num_aud_med);

        for _ in 0..num_aud_med {
            let (enc_sk, enc_pk) = keygen_enc(&mut rng, enc_key_gen);
            keypairs.push((enc_pk.0, enc_sk.0));
            pub_keys.push(enc_pk.0);
        }

        let nonce = b"test-aud-med-nonce";

        let proof = AudMedRegProof::new(
            &mut rng,
            keypairs,
            nonce,
            enc_key_gen
        ).unwrap();

        proof.verify(
            pub_keys.clone(),
            nonce,
            enc_key_gen
        ).unwrap();

        // Fail when less keys are provided
        let fewer_public_keys = pub_keys[..3].to_vec();
        let result = proof.verify(
            fewer_public_keys,
            nonce,
            enc_key_gen
        );
        assert!(result.is_err());

        // Fail when wrong keys are provided
        let mut wrong_public_keys = pub_keys.clone();
        wrong_public_keys[0] = PallasA::rand(&mut rng);
        let result = proof.verify(
            wrong_public_keys,
            nonce,
            enc_key_gen
        );
        assert!(result.is_err());

        // Fail when wrong generator is provided
        let wrong_enc_gen = PallasA::rand(&mut rng);
        let result = proof.verify(
            pub_keys,
            nonce,
            wrong_enc_gen
        );
        assert!(result.is_err());
    }
}