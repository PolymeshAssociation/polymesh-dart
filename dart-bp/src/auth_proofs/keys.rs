use crate::error::{Error, Result};
use crate::{NONCE_LABEL, TXN_CHALLENGE_LABEL, add_to_transcript};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{One, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    UniformRand,
    string::ToString,
    {vec, vec::Vec},
};
use core::ops::Neg;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use hkdf::hmac::Hmac;
use hkdf::{HkdfExtract, HmacImpl};
use polymesh_dart_common::{AssetId, NullifierSkGenCounter, SkGenCounter};
use rand_core::CryptoRngCore;
use sha2::{Digest, Sha256};
use zeroize::{Zeroize, ZeroizeOnDrop};

pub const T_SIG_KEY: &'static [u8; 9] = b"t_sig_key";
pub const T_ENC_KEY: &'static [u8; 9] = b"t_enc_key";

/// Add a slice to transcript by first writing the slice length (as index) and then each element
fn add_slice_to_transcript<T: CanonicalSerialize>(
    transcript: &mut MerlinTranscript,
    label: &'static [u8],
    slice: &[T],
) -> Result<()> {
    let l = slice.len() as u32;
    transcript.append(label, &l.to_le_bytes());

    let mut buf = vec![];
    for (i, item) in slice.iter().enumerate() {
        // Write the index and then the item
        buf.extend_from_slice(&(i as u32).to_le_bytes());
        item.serialize_compressed(&mut buf)?;
        transcript.append(label, &buf);
        buf.clear()
    }

    Ok(())
}

#[derive(Copy, Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq, Hash)]
pub struct VerKey<PK: AffineRepr>(pub PK);

#[derive(
    Clone,
    Debug,
    Default,
    CanonicalSerialize,
    CanonicalDeserialize,
    PartialEq,
    Eq,
    Zeroize,
    ZeroizeOnDrop,
)]
pub struct SigKey<PK: AffineRepr>(pub PK::ScalarField);

#[derive(Copy, Clone, Debug, CanonicalSerialize, CanonicalDeserialize, PartialEq, Eq, Hash)]
pub struct EncKey<PK: AffineRepr>(pub PK);

#[derive(
    Clone,
    Debug,
    Default,
    CanonicalSerialize,
    CanonicalDeserialize,
    PartialEq,
    Eq,
    Zeroize,
    ZeroizeOnDrop,
)]
pub struct DecKey<PK: AffineRepr>(pub PK::ScalarField);

pub fn rand_non_zero<F: Zero + UniformRand, R: CryptoRngCore>(rng: &mut R) -> F {
    loop {
        let f = F::rand(rng);
        if !f.is_zero() {
            return f;
        }
    }
}

pub fn keygen_sig<R: CryptoRngCore, PK: AffineRepr>(
    rng: &mut R,
    j: PK,
) -> (SigKey<PK>, VerKey<PK>) {
    let s = rand_non_zero::<PK::ScalarField, R>(rng);
    keygen_sig_given_sk(s, j)
}

pub fn keygen_sig_given_sk<PK: AffineRepr>(sk: PK::ScalarField, j: PK) -> (SigKey<PK>, VerKey<PK>) {
    let p = j * sk;
    (SigKey(sk), VerKey(p.into_affine()))
}

// NOTE: Same as above but just in case we need to use a diff. scheme
pub fn keygen_enc<R: CryptoRngCore, PK: AffineRepr>(
    rng: &mut R,
    g: PK,
) -> (DecKey<PK>, EncKey<PK>) {
    let s = rand_non_zero::<PK::ScalarField, R>(rng);
    keygen_enc_given_sk(s, g)
}

pub fn keygen_enc_given_sk<PK: AffineRepr>(sk: PK::ScalarField, g: PK) -> (DecKey<PK>, EncKey<PK>) {
    let p = g * sk;
    (DecKey(sk), EncKey(p.into_affine()))
}

const INVESTOR_KEY_REG_TXN_LABEL: &'static [u8; 25] = b"investor-key-registration";

const AUD_MED_KEY_REG_TXN_LABEL: &'static [u8; 33] = b"auditor/mediator-key-registration";

/// Register keys for 1 or more investors. For each investor, we have a signature and an encryption key.
/// Uses Batch Schnorr protocol from Fig. 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
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
        enc_key_gen: G,
    ) -> Result<Self> {
        // Note: This proof can be reduced to half in size if both sig and enc keys use the same generator
        let transcript = MerlinTranscript::new(INVESTOR_KEY_REG_TXN_LABEL);
        Self::new_with_given_transcript(rng, keys, nonce, sig_key_gen, enc_key_gen, transcript)
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        mut keys: Vec<((G, G::ScalarField), (G, G::ScalarField))>,
        nonce: &[u8],
        sig_key_gen: G,
        enc_key_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<Self> {
        // Note: This proof can be reduced to half in size if both sig and enc keys use the same generator

        add_to_transcript!(transcript, NONCE_LABEL, nonce);

        let key_pairs: Vec<_> = keys.iter().map(|((s, _), (e, _))| (*s, *e)).collect();
        add_slice_to_transcript(&mut transcript, b"keys", &key_pairs)?;

        let mut r_sig = G::ScalarField::rand(rng);
        let mut r_enc = G::ScalarField::rand(rng);

        let t_sig = (sig_key_gen * r_sig).into_affine();
        let t_enc = (enc_key_gen * r_enc).into_affine();

        add_to_transcript!(transcript, T_SIG_KEY, t_sig, T_ENC_KEY, t_enc);

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut s_sig = r_sig;
        let mut s_enc = r_enc;

        r_sig.zeroize();
        r_enc.zeroize();

        let mut c = challenge;
        for ((_, s), (_, e)) in keys.iter_mut() {
            s_sig += c * *s;
            s_enc += c * *e;
            c = c * challenge;
            s.zeroize();
            e.zeroize();
        }

        Ok(Self {
            sig: (t_sig, s_sig),
            enc: (t_enc, s_enc),
        })
    }

    /// Each item of `keys` is a pair where the first element is the signing public key and the
    /// second element is the encryption public key
    pub fn verify(
        &self,
        pub_keys: Vec<(G, G)>,
        nonce: &[u8],
        sig_key_gen: G,
        enc_key_gen: G,
    ) -> Result<()> {
        let transcript = MerlinTranscript::new(INVESTOR_KEY_REG_TXN_LABEL);
        self.verify_with_given_transcript(pub_keys, nonce, sig_key_gen, enc_key_gen, transcript)
    }

    pub fn verify_with_given_transcript(
        &self,
        pub_keys: Vec<(G, G)>,
        nonce: &[u8],
        sig_key_gen: G,
        enc_key_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<()> {
        for (a, e) in pub_keys.iter() {
            if a.is_zero() || e.is_zero() {
                return Err(Error::PointAtIdentity);
            }
        }
        add_to_transcript!(transcript, NONCE_LABEL, nonce);

        add_slice_to_transcript(&mut transcript, b"keys", &pub_keys)?;

        add_to_transcript!(transcript, T_SIG_KEY, self.sig.0, T_ENC_KEY, self.enc.0);

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

        sig_keys.push(sig_key_gen);
        challenge_powers.push(-self.sig.1);
        if self.sig.0.into_group().neg() != G::Group::msm_unchecked(&sig_keys, &challenge_powers) {
            return Err(Error::ProofVerificationError(
                "Signature key proof verification failed".to_string(),
            ));
        }

        enc_keys.push(enc_key_gen);
        challenge_powers[enc_keys.len() - 1] = -self.enc.1;
        if self.enc.0.into_group().neg() != G::Group::msm_unchecked(&enc_keys, &challenge_powers) {
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
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
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
        enc_key_gen: G,
    ) -> Result<Self> {
        let transcript = MerlinTranscript::new(AUD_MED_KEY_REG_TXN_LABEL);
        Self::new_with_given_transcript(rng, keys, nonce, enc_key_gen, transcript)
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        mut keys: Vec<(G, G::ScalarField)>,
        nonce: &[u8],
        enc_key_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<Self> {
        add_to_transcript!(transcript, NONCE_LABEL, nonce);

        let enc_keys: Vec<_> = keys.iter().map(|(e, _)| *e).collect();
        add_slice_to_transcript(&mut transcript, b"keys", &enc_keys)?;

        let mut r = G::ScalarField::rand(rng);
        let t = (enc_key_gen * r).into_affine();

        add_to_transcript!(transcript, T_ENC_KEY, t);

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut s = r;
        r.zeroize();
        let mut c = challenge;
        for (_, e) in keys.iter_mut() {
            s += c * *e;
            c = c * challenge;
            e.zeroize();
        }

        Ok(Self { t, s })
    }

    pub fn verify(&self, pub_keys: Vec<G>, nonce: &[u8], enc_key_gen: G) -> Result<()> {
        let transcript = MerlinTranscript::new(AUD_MED_KEY_REG_TXN_LABEL);
        self.verify_with_given_transcript(pub_keys, nonce, enc_key_gen, transcript)
    }

    pub fn verify_with_given_transcript(
        &self,
        pub_keys: Vec<G>,
        nonce: &[u8],
        enc_key_gen: G,
        mut transcript: MerlinTranscript,
    ) -> Result<()> {
        for k in pub_keys.iter() {
            if k.is_zero() {
                return Err(Error::PointAtIdentity);
            }
        }
        add_to_transcript!(transcript, NONCE_LABEL, nonce);

        add_slice_to_transcript(&mut transcript, b"keys", &pub_keys)?;

        add_to_transcript!(transcript, T_ENC_KEY, self.t);

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut enc_keys = vec![];
        let mut challenge_powers = vec![];
        let mut c = G::ScalarField::one();
        for e in pub_keys.into_iter() {
            enc_keys.push(e);
            c = c * challenge;
            challenge_powers.push(c);
        }

        enc_keys.push(enc_key_gen);
        challenge_powers.push(-self.s);
        if self.t.into_group().neg() != G::Group::msm_unchecked(&enc_keys, &challenge_powers) {
            return Err(Error::ProofVerificationError(
                "Encryption key proof verification failed".to_string(),
            ));
        }

        Ok(())
    }
}

/// `hkdf_to_field` domain for the account signing key.
pub const SIG_KEY_DST: &[u8] = b"POLYMESH-DART-V1-SIG-KEY";

/// `hkdf_to_field` domain for the account encryption key.
pub const ENC_KEY_DST: &[u8] = b"POLYMESH-DART-V1-ENC-KEY";

/// `hkdf_to_field` domain for non-fee account `(randomness, rho_randomness)`.
pub const ACCOUNT_RANDOMNESS_DST: &[u8] = b"POLYMESH-DART-V1-ACCOUNT-RANDOMNESS";

/// `hkdf_to_field` domain for fee account `(initial_rho, initial_randomness)`.
pub const FEE_ACCOUNT_RANDOMNESS_DST: &[u8] = b"POLYMESH-DART-V1-FEE-ACCOUNT-RANDOMNESS";

/// `N` nonzero field elements. The `i`-th is KeyGen of
/// [draft-irtf-cfrg-bls-signature-05](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-05#section-2.3)
/// Section 2.3 with `H = SHA-256`, `IKM = ikm`, `salt = dst`, `key_info = info || I2OSP(i, 1)` and
/// `r = p`.
pub fn hkdf_to_field<F: PrimeField, const N: usize>(
    dst: &[u8],
    ikm: &[u8],
    info: &[u8],
) -> Result<[F; N]> {
    let mut elems = [F::zero(); N];
    for (i, elem) in elems.iter_mut().enumerate() {
        *elem = ietf_keygen::<F, Sha256, Hmac<Sha256>>(dst, ikm, &[info, &[i as u8]])?;
    }
    Ok(elems)
}

/// Minimum IKM length of KeyGen.
pub const MIN_IKM_LEN: usize = 32;

/// KeyGen of draft-irtf-cfrg-bls-signature-05 Section 2.3 with hash `H` and HMAC `I`, `key_info`
/// the concatenation of `key_info`. Rejects `ikm` shorter than `MIN_IKM_LEN`.
fn ietf_keygen<F: PrimeField, H: Digest, I: HmacImpl<H>>(
    salt: &[u8],
    ikm: &[u8],
    key_info: &[&[u8]],
) -> Result<F> {
    if ikm.len() < MIN_IKM_LEN {
        return Err(Error::SeedTooShort(ikm.len(), MIN_IKM_LEN));
    }
    // L = ceil((3 * ceil(log2(r))) / 16)
    let l = (3 * F::MODULUS_BIT_SIZE as usize).div_ceil(16);
    let l_bytes = (l as u16).to_be_bytes();
    let mut info = key_info.to_vec();
    info.push(&l_bytes);
    let mut salt = salt.to_vec();
    let mut okm = vec![0u8; l];
    loop {
        // PRK = HKDF-Extract(salt, IKM || I2OSP(0, 1))
        let mut extract = HkdfExtract::<H, I>::new(Some(&salt));
        extract.input_ikm(ikm);
        extract.input_ikm(&[0]);
        let (mut prk, hkdf) = extract.finalize();
        prk[..].zeroize();
        // OKM = HKDF-Expand(PRK, key_info || I2OSP(L, 2), L)
        hkdf.expand_multi_info(&info, &mut okm)
            .expect("L is at most 255 * H output size");
        // SK = OS2IP(OKM) mod r
        let sk = F::from_be_bytes_mod_order(&okm);
        if !sk.is_zero() {
            okm.zeroize();
            return Ok(sk);
        }
        salt = H::digest(&salt).to_vec();
    }
}

/// Appends `bytes` with a `u32` little-endian length prefix.
fn extend_with_len(buf: &mut Vec<u8>, bytes: &[u8]) {
    buf.extend((bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(bytes);
}

/// Seed a Ledger-class device derives account keys and per-account randomness from, so the device
/// never has to persist secret keys.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct MasterSeed(Vec<u8>);

impl MasterSeed {
    pub fn new(seed: Vec<u8>) -> Self {
        Self(seed)
    }

    /// Doesn't include asset-id to allow accounts to share secret keys
    pub fn derive_keys<G: AffineRepr>(
        &self,
        path: &[u8],
        counter: SkGenCounter,
        j: G,
        g: G,
    ) -> Result<((SigKey<G>, VerKey<G>), (DecKey<G>, EncKey<G>))> {
        // For creating secret keys, use info `len(path) || path || counter`
        let mut info = Vec::new();
        extend_with_len(&mut info, path);
        info.extend(counter.to_le_bytes());

        let [sig_sk] = hkdf_to_field::<G::ScalarField, 1>(SIG_KEY_DST, &self.0, &info)?;
        let [enc_sk] = hkdf_to_field::<G::ScalarField, 1>(ENC_KEY_DST, &self.0, &info)?;

        let (sk, vk) = keygen_sig_given_sk(sig_sk, j);
        let (dk, ek) = keygen_enc_given_sk(enc_sk, g);

        Ok(((sk, vk), (dk, ek)))
    }

    /// Returns `(randomness, rho_randomness)` where `randomness` is for the account commitment
    /// and `rho_randomness` is used to derive `rho`. Differs from the host's
    /// `AccountKeyPair::derive_account_randomness` for the same keys. An account opened with this
    /// is recoverable only from the seed and path.
    pub fn derive_account_randomness<G: AffineRepr>(
        &self,
        path: &[u8],
        counter_s: SkGenCounter,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> Result<(G::ScalarField, G::ScalarField)> {
        self.derive_randomness::<G>(ACCOUNT_RANDOMNESS_DST, path, counter_s, asset_id, counter)
    }

    /// Returns `(initial_rho, initial_randomness)` for a fee account, from the same input as
    /// `derive_account_randomness` under a separate domain. The first output is `initial_rho`, not
    /// the commitment randomness as in `derive_account_randomness`. Differs from the host's
    /// `AccountKeyPair::derive_fee_account_randomness` for the same keys.
    pub fn derive_fee_account_randomness<G: AffineRepr>(
        &self,
        path: &[u8],
        counter_s: SkGenCounter,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> Result<(G::ScalarField, G::ScalarField)> {
        self.derive_randomness::<G>(
            FEE_ACCOUNT_RANDOMNESS_DST,
            path,
            counter_s,
            asset_id,
            counter,
        )
    }

    fn derive_randomness<G: AffineRepr>(
        &self,
        dst: &[u8],
        path: &[u8],
        counter_s: SkGenCounter,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> Result<(G::ScalarField, G::ScalarField)> {
        // For creating randomness, use info `len(path) || path || counter_s || asset_id || counter_n`
        let mut info = Vec::new();
        extend_with_len(&mut info, path);
        info.extend(counter_s.to_le_bytes());
        info.extend(asset_id.to_le_bytes());
        info.extend(counter.to_le_bytes());
        // Need two independent field elements, `randomness`, `rho_randomness`
        let [randomness, rho_randomness] = hkdf_to_field::<G::ScalarField, 2>(dst, &self.0, &info)?;
        Ok((randomness, rho_randomness))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::keys::{keygen_enc, keygen_sig};
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    type PallasA = ark_pallas::Affine;

    #[test]
    fn investor_key_reg_proof() {
        // Happy path for the investor (sig+enc) key-registration proof, plus rejection when given too few keys, a wrong pubkey, or swapped generators.
        let mut rng = StdRng::seed_from_u64(0);

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

        let proof =
            InvestorKeyRegProof::new(&mut rng, keypairs, nonce, sig_key_gen, enc_key_gen).unwrap();

        proof
            .verify(pub_keys.clone(), nonce, sig_key_gen, enc_key_gen)
            .unwrap();

        // Fail when less keys are provided
        let fewer_public_keys = pub_keys[..3].to_vec();
        let result = proof.verify(fewer_public_keys, nonce, sig_key_gen, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong keys are provided
        let mut wrong_public_keys = pub_keys.clone();
        wrong_public_keys[0] = (PallasA::rand(&mut rng), PallasA::rand(&mut rng));
        let result = proof.verify(wrong_public_keys, nonce, sig_key_gen, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong generators are provided
        let result = proof.verify(pub_keys, nonce, enc_key_gen, sig_key_gen);
        assert!(result.is_err());
    }

    #[test]
    fn investor_key_reg_proof_order() {
        // Like investor_key_reg_proof but checks the proof binds the ORDER of the keys: swapping two pubkeys, or duplicating one, must fail verification.
        let mut rng = StdRng::seed_from_u64(0);
        let nonce = b"test_nonce_1";

        for _ in 0..5 {
            let num_investors = 6;
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

            let proof =
                InvestorKeyRegProof::new(&mut rng, keypairs, nonce, sig_key_gen, enc_key_gen)
                    .unwrap();

            proof
                .verify(pub_keys.clone(), nonce, sig_key_gen, enc_key_gen)
                .unwrap();

            let mut swapped_public_keys = pub_keys.clone();
            swapped_public_keys.swap(1, 2);
            let result = proof.verify(swapped_public_keys, nonce, sig_key_gen, enc_key_gen);
            assert!(result.is_err());

            let mut duplicated_public_keys = pub_keys;
            duplicated_public_keys[1] = duplicated_public_keys[0];
            let result = proof.verify(duplicated_public_keys, nonce, sig_key_gen, enc_key_gen);
            assert!(result.is_err());
        }
    }

    #[test]
    fn aud_med_key_reg_proof() {
        // Happy path for the auditor/mediator (enc-key-only) registration proof, plus rejection on too few keys, a wrong pubkey, or a wrong generator.
        let mut rng = StdRng::seed_from_u64(0);

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

        let proof = AudMedRegProof::new(&mut rng, keypairs, nonce, enc_key_gen).unwrap();

        proof.verify(pub_keys.clone(), nonce, enc_key_gen).unwrap();

        // Fail when less keys are provided
        let fewer_public_keys = pub_keys[..3].to_vec();
        let result = proof.verify(fewer_public_keys, nonce, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong keys are provided
        let mut wrong_public_keys = pub_keys.clone();
        wrong_public_keys[0] = PallasA::rand(&mut rng);
        let result = proof.verify(wrong_public_keys, nonce, enc_key_gen);
        assert!(result.is_err());

        // Fail when wrong generator is provided
        let wrong_enc_gen = PallasA::rand(&mut rng);
        let result = proof.verify(pub_keys, nonce, wrong_enc_gen);
        assert!(result.is_err());
    }

    #[test]
    fn aud_med_key_reg_proof_order() {
        // Like aud_med_key_reg_proof but checks the proof binds key ORDER: swapping two pubkeys, or duplicating one, must fail verification.
        let mut rng = StdRng::seed_from_u64(0);
        let nonce = b"test_nonce_3";

        for _ in 0..5 {
            let num_aud_med = 6;
            let enc_key_gen = PallasA::rand(&mut rng);

            let mut keypairs = Vec::with_capacity(num_aud_med);
            let mut pub_keys = Vec::with_capacity(num_aud_med);

            for _ in 0..num_aud_med {
                let (enc_sk, enc_pk) = keygen_enc(&mut rng, enc_key_gen);
                keypairs.push((enc_pk.0, enc_sk.0));
                pub_keys.push(enc_pk.0);
            }

            let proof = AudMedRegProof::new(&mut rng, keypairs, nonce, enc_key_gen).unwrap();

            proof.verify(pub_keys.clone(), nonce, enc_key_gen).unwrap();

            let mut swapped_public_keys = pub_keys.clone();
            swapped_public_keys.swap(1, 2);
            let result = proof.verify(swapped_public_keys, nonce, enc_key_gen);
            assert!(result.is_err());

            let mut duplicated_public_keys = pub_keys;
            duplicated_public_keys[1] = duplicated_public_keys[0];
            let result = proof.verify(duplicated_public_keys, nonce, enc_key_gen);
            assert!(result.is_err());
        }
    }

    #[test]
    fn keygen_matches_eip2333_master_sk() {
        // EIP-2333 `derive_master_SK` test cases 0-3 (https://eips.ethereum.org/EIPS/eip-2333#test-cases).
        // `HKDF_mod_r` is KeyGen with `H = SHA-256` and `salt = H("BLS-SIG-KEYGEN-SALT-")`.
        use ark_std::str::FromStr;
        use sha2::Sha256;
        type Fr = ark_bls12_381::Fr;

        let salt = Sha256::digest(b"BLS-SIG-KEYGEN-SALT-");
        for (seed, master_sk) in [
            (
                "c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04",
                "6083874454709270928345386274498605044986640685124978867557563392430687146096",
            ),
            (
                "3141592653589793238462643383279502884197169399375105820974944592",
                "29757020647961307431480504535336562678282505419141012933316116377660817309383",
            ),
            (
                "0099FF991111002299DD7744EE3355BBDD8844115566CC55663355668888CC00",
                "27580842291869792442942448775674722299803720648445448686099262467207037398656",
            ),
            (
                "d4e56740f876aef8c010b86a40d5f56745a118d0906a34e69aec8c0db1cb8fa3",
                "19022158461524446591288038168518313374041767046816487870552872741050760015818",
            ),
        ] {
            let sk =
                ietf_keygen::<Fr, Sha256, Hmac<Sha256>>(&salt, &hex::decode(seed).unwrap(), &[])
                    .unwrap();
            assert_eq!(sk, Fr::from_str(master_sk).unwrap());
        }
    }

    #[test]
    fn keygen_rejects_short_ikm() {
        let seed = MasterSeed::new([1u8; MIN_IKM_LEN - 1].to_vec());
        let j = PallasA::rand(&mut StdRng::seed_from_u64(0));
        let g = PallasA::rand(&mut StdRng::seed_from_u64(1));
        assert!(matches!(
            seed.derive_keys::<PallasA>(b"path", 0, j, g),
            Err(Error::SeedTooShort(31, 32))
        ));
        let seed = MasterSeed::new([1u8; MIN_IKM_LEN].to_vec());
        seed.derive_keys::<PallasA>(b"path", 0, j, g).unwrap();
    }

    #[test]
    fn keygen_matches_blst_key_gen_v5() {
        // Big-endian `SecretKey::key_gen_v5(&[7; 32], salt, key_info).to_bytes()` of blst 0.3.17.
        use sha2::Sha256;
        type Fr = ark_bls12_381::Fr;

        for (salt, key_info, sk) in [
            (
                &b"POLYMESH-DART-V1-SIG-KEY"[..],
                &b""[..],
                "33883e510250228d8ea938a903b732ff32c9c92f82a4cefc51302c4b11aa5729",
            ),
            (
                &b"POLYMESH-DART-V1-SIG-KEY"[..],
                &[0u8; 7][..],
                "39c951bd8f0d78b05e29f7af6aea934981c55732696d20136c30008b8cc0feae",
            ),
            (
                &b"POLYMESH-DART-V1-ACCOUNT-RANDOMNESS"[..],
                &b"abc\x01"[..],
                "04d7cd8346ca83b5ecf2084883638f4d1378e8441f2982b4f49bec1d19c3298c",
            ),
        ] {
            let got =
                ietf_keygen::<Fr, Sha256, Hmac<Sha256>>(salt, &[7u8; 32], &[key_info]).unwrap();
            assert_eq!(got, Fr::from_be_bytes_mod_order(&hex::decode(sk).unwrap()));
        }
    }

    #[test]
    fn master_seed_derivation_deterministic_and_domain_separated() {
        // Seed-derived keys/randomness are deterministic: same (seed,path,counter) reproduces identical output, and changing seed, path,
        // or counter yields different keys/randomness — domain separation across the derivation inputs.
        let mut rng = StdRng::seed_from_u64(0);

        let asset_id = 1;
        let counter_s = 1;
        let counter_n = 1;

        let seed1 = MasterSeed::new([1u8; 32].to_vec());
        let seed2 = MasterSeed::new([2u8; 32].to_vec());

        let j = PallasA::rand(&mut rng);
        let g = PallasA::rand(&mut rng);

        let result1 = seed1
            .derive_keys::<PallasA>(b"path", counter_s, j, g)
            .unwrap();
        let result2 = seed1
            .derive_keys::<PallasA>(b"path", counter_s, j, g)
            .unwrap();
        assert_eq!(result1, result2);

        // Same seed, different path
        let result3 = seed1
            .derive_keys::<PallasA>(b"path1", counter_s, j, g)
            .unwrap();
        assert_ne!(result1, result3);

        // Same seed, same path, different counter
        let result4 = seed1
            .derive_keys::<PallasA>(b"path", counter_s + 1, j, g)
            .unwrap();
        assert_ne!(result1, result4);

        // Different seed, same path and counter
        let result5 = seed2
            .derive_keys::<PallasA>(b"path", counter_s, j, g)
            .unwrap();
        assert_ne!(result1, result5);

        // Returns (randomness, rho_randomness) tuple
        let rand1 = seed1
            .derive_account_randomness::<PallasA>(b"path", counter_s, asset_id, counter_n)
            .unwrap();
        let rand2 = seed1
            .derive_account_randomness::<PallasA>(b"path", counter_s, asset_id, counter_n)
            .unwrap();
        assert_eq!(rand1, rand2);

        // Different counter
        let rand3 = seed1
            .derive_account_randomness::<PallasA>(b"path", counter_s, asset_id, counter_n + 1)
            .unwrap();
        assert_ne!(rand1, rand3);

        let rand4 = seed1
            .derive_account_randomness::<PallasA>(b"path", counter_s + 1, asset_id, counter_n)
            .unwrap();
        assert_ne!(rand1, rand4);

        let rand5 = seed1
            .derive_account_randomness::<PallasA>(b"path1", counter_s, asset_id, counter_n)
            .unwrap();
        assert_ne!(rand1, rand5);

        let rand6 = seed2
            .derive_account_randomness::<PallasA>(b"path", counter_s, asset_id, counter_n)
            .unwrap();
        assert_ne!(rand1, rand6);

        let fee1 = seed1
            .derive_fee_account_randomness::<PallasA>(b"path", counter_s, asset_id, counter_n)
            .unwrap();
        let fee2 = seed1
            .derive_fee_account_randomness::<PallasA>(b"path", counter_s, asset_id, counter_n)
            .unwrap();
        assert_eq!(fee1, fee2);

        // Same input as `derive_account_randomness`, separate domain
        assert_ne!(fee1.0, rand1.0);
        assert_ne!(fee1.0, rand1.1);
        assert_ne!(fee1.1, rand1.0);
        assert_ne!(fee1.1, rand1.1);

        let fee3 = seed1
            .derive_fee_account_randomness::<PallasA>(b"path", counter_s, asset_id, counter_n + 1)
            .unwrap();
        assert_ne!(fee1, fee3);
    }
}
