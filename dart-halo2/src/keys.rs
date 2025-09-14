use std::ops::Neg;
use crate::AffineSerializable;
use crate::error::{Error, Result};
use crate::types_and_constants::{TXN_CHALLENGE_LABEL, TXN_INSTANCE_LABEL};
use crate::utils::TranscriptWriter;
use ark_std::vec::Vec;
use ff::Field;
use group::Curve;
use merlin::Transcript;
use multiexp::multiexp_vartime;
use rand_core::CryptoRngCore;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct VerKey<PK: AffineSerializable>(pub PK);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SigKey<PK: AffineSerializable>(pub PK::ScalarExt);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EncKey<PK: AffineSerializable>(pub PK);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct DecKey<PK: AffineSerializable>(pub PK::ScalarExt);

pub fn keygen_sig<R: CryptoRngCore, PK: AffineSerializable>(
    rng: &mut R,
    j: PK,
) -> (SigKey<PK>, VerKey<PK>) {
    let s = PK::ScalarExt::random(rng);
    let p = j * s;
    (SigKey(s), VerKey(p.to_affine()))
}

// NOTE: Same as above but just in case we need to use a diff. scheme
pub fn keygen_enc<R: CryptoRngCore, PK: AffineSerializable>(
    rng: &mut R,
    g: PK,
) -> (DecKey<PK>, EncKey<PK>) {
    let s = PK::ScalarExt::random(rng);
    let p = g * s;
    (DecKey(s), EncKey(p.to_affine()))
}

const INVESTOR_KEY_REG_TXN_LABEL: &'static [u8; 25] = b"investor-key-registration";
const AUD_MED_KEY_REG_TXN_LABEL: &'static [u8; 33] = b"auditor/mediator-key-registration";

/// Register keys for 1 or more investors. For each investor, we have a signature and an encryption key.
/// Uses Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf)
pub struct InvestorKeyRegProof<G: AffineSerializable> {
    pub sig: (G, G::Scalar),
    pub enc: (G, G::Scalar),
}

impl<G: AffineSerializable> InvestorKeyRegProof<G>
where
    G::Repr: AsRef<[u8]>,
{
    /// Each item of `keys` is a pair where the first element is the pair of signing public
    /// and secret key and the second element is the pair of encryption public and secret key.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        keys: Vec<((G, G::Scalar), (G, G::Scalar))>,
        nonce: &[u8],
        sig_key_gen: G,
        enc_key_gen: G,
    ) -> Result<Self> {
        let mut transcript = Transcript::new(INVESTOR_KEY_REG_TXN_LABEL);
        let mut extra_instance = Vec::new();

        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(sig_key_gen.to_bytes().as_ref());
        extra_instance.extend_from_slice(enc_key_gen.to_bytes().as_ref());

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        for ((s, _), (e, _)) in keys.iter() {
            transcript_writer.append_serializable(s)?;
            transcript_writer.append_serializable(e)?;
        }

        let r_sig = G::Scalar::random(&mut *rng);
        let r_enc = G::Scalar::random(rng);

        let t_sig = (sig_key_gen * r_sig).to_affine();
        let t_enc = (enc_key_gen * r_enc).to_affine();

        // Append commitments to extra_instance
        extra_instance.extend_from_slice(t_sig.to_bytes().as_ref());
        extra_instance.extend_from_slice(t_enc.to_bytes().as_ref());

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let mut s_sig = r_sig;
        let mut s_enc = r_enc;

        let mut c = challenge;
        for ((_, s), (_, e)) in keys.into_iter() {
            s_sig += c * s;
            s_enc += c * e;
            c = c * challenge;
        }

        Ok(Self {
            sig: (t_sig, s_sig),
            enc: (t_enc, s_enc),
        })
    }

    pub fn verify(
        &self,
        keys: Vec<(G, G)>,
        nonce: &[u8],
        sig_key_gen: G,
        enc_key_gen: G,
    ) -> Result<()> {
        let mut transcript = Transcript::new(INVESTOR_KEY_REG_TXN_LABEL);
        let mut extra_instance = Vec::new();

        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(sig_key_gen.to_bytes().as_ref());
        extra_instance.extend_from_slice(enc_key_gen.to_bytes().as_ref());

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        for (s, e) in keys.iter() {
            transcript_writer.append_serializable(s)?;
            transcript_writer.append_serializable(e)?;
        }

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let mut sig_pairs = Vec::new();
        let mut enc_pairs = Vec::new();
        let mut challenge_powers = Vec::new();
        let mut c = challenge;
        for (s, e) in keys.into_iter() {
            challenge_powers.push(c);
            sig_pairs.push((c, s.to_curve()));
            enc_pairs.push((c, e.to_curve()));
            c = c * challenge;
        }

        // Even the following 2 checks can be combined into 1 with RLC

        // Verify signature key proof
        sig_pairs.push((-self.sig.1, sig_key_gen.to_curve()));
        if multiexp_vartime(&sig_pairs) != self.sig.0.to_curve().neg() {
            return Err(Error::ProofVerificationError(
                "Signature key proof verification failed".to_string(),
            ));
        }

        // Verify encryption key proof
        enc_pairs.push((-self.enc.1, enc_key_gen.to_curve()));
        if multiexp_vartime(&enc_pairs) != self.enc.0.to_curve().neg() {
            return Err(Error::ProofVerificationError(
                "Encryption key proof verification failed".to_string(),
            ));
        }

        Ok(())
    }
}

/// Register keys for 1 or more auditor/mediator. For each auditor/mediator key, we have an encryption key.
/// Supporting registering multiple keys as an entity might use different assets and roles (like delegating in an org)
/// Uses Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf)
pub struct AudMedRegProof<G: AffineSerializable> {
    pub t: G,
    pub s: G::Scalar,
}

impl<G: AffineSerializable> AudMedRegProof<G> {
    /// Each item of `keys` is a pair of encryption public and secret key.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        keys: Vec<(G, G::Scalar)>,
        nonce: &[u8],
        enc_key_gen: G,
    ) -> Result<Self> {
        let mut transcript = Transcript::new(AUD_MED_KEY_REG_TXN_LABEL);
        let mut extra_instance = Vec::new();

        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(enc_key_gen.to_bytes().as_ref());

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        for (e, _) in keys.iter() {
            transcript_writer.append_serializable(e)?;
        }

        let r = G::Scalar::random(rng);
        let t = (enc_key_gen * r).to_affine();

        extra_instance.extend_from_slice(t.to_bytes().as_ref());

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let mut s = r;
        let mut c = challenge;
        for (_, e) in keys.into_iter() {
            s += c * e;
            c = c * challenge;
        }

        Ok(Self { t, s })
    }

    pub fn verify(&self, keys: Vec<G>, nonce: &[u8], enc_key_gen: G) -> Result<()> {
        let mut transcript = Transcript::new(AUD_MED_KEY_REG_TXN_LABEL);
        let mut extra_instance = Vec::new();

        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(enc_key_gen.to_bytes().as_ref());

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        for e in keys.iter() {
            transcript_writer.append_serializable(e)?;
        }

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let mut enc_pairs = Vec::new();
        let mut challenge_powers = Vec::new();
        let mut c = challenge;
        for e in keys.into_iter() {
            challenge_powers.push(c);
            enc_pairs.push((c, e.to_curve()));
            c = c * challenge;
        }

        // Verify encryption key proof
        enc_pairs.push((-self.s, enc_key_gen.to_curve()));
        if multiexp_vartime(&enc_pairs) != self.t.to_curve().neg() {
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
    use group::Group;
    use pasta_curves::pallas::Point as PallasPoint;

    #[test]
    fn investor_key_reg_proof() {
        let mut rng = rand::thread_rng();

        let num_investors = 5;

        let sig_key_gen = PallasPoint::random(&mut rng).to_affine();
        let enc_key_gen = PallasPoint::random(&mut rng).to_affine();

        let mut keypairs = Vec::with_capacity(num_investors);
        let mut public_keys = Vec::with_capacity(num_investors);

        for _ in 0..num_investors {
            let (sig_sk, sig_pk) = keygen_sig(&mut rng, sig_key_gen);
            let (enc_sk, enc_pk) = keygen_enc(&mut rng, enc_key_gen);
            keypairs.push(((sig_pk.0, sig_sk.0), (enc_pk.0, enc_sk.0)));
            public_keys.push((sig_pk.0, enc_pk.0));
        }

        let nonce = b"test-nonce";

        let proof =
            InvestorKeyRegProof::new(&mut rng, keypairs, nonce, sig_key_gen, enc_key_gen).unwrap();

        proof
            .verify(public_keys.clone(), nonce, sig_key_gen, enc_key_gen)
            .unwrap();

        // Fail when less keys are provided
        let fewer_public_keys = public_keys[..3].to_vec();
        let result = proof.verify(fewer_public_keys, nonce, sig_key_gen, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong keys are provided
        let mut wrong_public_keys = public_keys.clone();
        wrong_public_keys[0] = (
            PallasPoint::random(&mut rng).to_affine(),
            PallasPoint::random(&mut rng).to_affine(),
        );
        let result = proof.verify(wrong_public_keys, nonce, sig_key_gen, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong generators are provided
        let result = proof.verify(public_keys, nonce, enc_key_gen, sig_key_gen);
        assert!(result.is_err());
    }

    #[test]
    fn aud_med_key_reg_proof() {
        let mut rng = rand::thread_rng();

        let num_aud_med = 5;

        let enc_key_gen = PallasPoint::random(&mut rng).to_affine();

        let mut keypairs = Vec::with_capacity(num_aud_med);
        let mut public_keys = Vec::with_capacity(num_aud_med);

        for _ in 0..num_aud_med {
            let (enc_sk, enc_pk) = keygen_enc(&mut rng, enc_key_gen);
            keypairs.push((enc_pk.0, enc_sk.0));
            public_keys.push(enc_pk.0);
        }

        let nonce = b"test-aud-med-nonce";

        let proof = AudMedRegProof::new(&mut rng, keypairs, nonce, enc_key_gen).unwrap();

        proof
            .verify(public_keys.clone(), nonce, enc_key_gen)
            .unwrap();

        // Fail when less keys are provided
        let fewer_public_keys = public_keys[..3].to_vec();
        let result = proof.verify(fewer_public_keys, nonce, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong keys are provided
        let mut wrong_public_keys = public_keys.clone();
        wrong_public_keys[0] = PallasPoint::random(&mut rng).to_affine();
        let result = proof.verify(wrong_public_keys, nonce, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong generator is provided
        let wrong_enc_gen = PallasPoint::random(&mut rng).to_affine();
        let result = proof.verify(public_keys, nonce, wrong_enc_gen);
        assert!(result.is_err());
    }
}
