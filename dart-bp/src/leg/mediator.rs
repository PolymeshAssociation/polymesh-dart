use crate::leg::{MediatorEncryption, MediatorEncryptionOld};
use crate::{Error, LEG_ENC_LABEL, NONCE_LABEL, add_to_transcript, error::Result};
use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ec::scalar_mul::BatchMulPreprocessing;
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::string::ToString;
use ark_std::{vec, vec::Vec};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use zeroize::Zeroize;

/// Transcript domain of the ring affirmation used when asset-id is hidden.
pub const MEDIATOR_TXN_LABEL: &[u8; 17] = b"mediator-txn-ring";
/// Transcript domain of the affirmation that predates the broadcast scheme. Its value must stay as
/// it was or legs created under that scheme stop verifying.
pub const MEDIATOR_TXN_OLD_LABEL: &[u8; 12] = b"mediator-txn";
pub const MEDIATOR_TXN_OLD_CHALLENGE_LABEL: &[u8; 22] = b"mediator-txn-challenge";
/// Transcript domain of the affirmation used when asset-id is revealed.
pub const PUBLIC_MEDIATOR_TXN_LABEL: &[u8; 25] = b"mediator-txn-public-asset";
pub const MEDIATOR_INDEX_LABEL: &[u8; 14] = b"mediator-index";
pub const MEDIATOR_TXN_RESPONSE_LABEL: &[u8; 17] = b"mediator-response";
pub const MEDIATOR_TXN_ACCEPT_RESPONSE: &[u8; 6] = b"accept";
pub const MEDIATOR_TXN_REJECT_RESPONSE: &[u8; 6] = b"reject";

/// CDS 1-of-n OR over sigma protocol: proves `y = base1_k * w1 + base2 * w2` for a hidden `k`,
/// where `base2` and `y` are shared across branches.
/// Follows the protocol of Theorem 8 and Corollary 12 of [Proofs of Partial Knowledge and Simplified Design of Witness Hiding Protocols](https://people.csail.mit.edu/rivest/voting/papers/CramerDamgardSchoenmakers-ProofsOfPartialKnowledge.pdf)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CdsOr<G: AffineRepr> {
    /// Challenges
    pub c: Vec<G::ScalarField>,
    /// Responses for witness 1
    pub s1: Vec<G::ScalarField>,
    /// Responses for witness 2
    pub s2: Vec<G::ScalarField>,
}

impl<G: AffineRepr> CdsOr<G> {
    // Optmz: Could use JSF

    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        mut w1: G::ScalarField,
        mut w2: G::ScalarField,
        real_idx: usize,
        y: G,
        bases1: &[G],
        base2: G,
        transcript: &mut MerlinTranscript,
    ) -> Self {
        let n = bases1.len();
        let zero = G::ScalarField::from(0u64);
        let mut c = vec![zero; n];
        let mut s1 = vec![zero; n];
        let mut s2 = vec![zero; n];
        let mut t = Vec::with_capacity(n);
        let mut r1 = zero;
        let mut r2 = zero;
        let base2_table = BatchMulPreprocessing::<G::Group>::new(base2.into_group(), n);
        let y_table = BatchMulPreprocessing::<G::Group>::new(y.into_group(), n);
        for (k, b1) in bases1.iter().enumerate() {
            let t_k = if k == real_idx {
                r1 = G::ScalarField::rand(rng);
                r2 = G::ScalarField::rand(rng);
                *b1 * r1 + base2_table.windowed_mul(&r2)
            } else {
                // Simulate
                c[k] = G::ScalarField::rand(rng);
                s1[k] = G::ScalarField::rand(rng);
                s2[k] = G::ScalarField::rand(rng);
                *b1 * s1[k] + base2_table.windowed_mul(&s2[k]) - y_table.windowed_mul(&c[k])
            };
            t.push(t_k);
        }
        let t = G::Group::normalize_batch(&t);
        let ch = Self::compute_challenge(y, bases1, base2, &t, transcript);
        let sum_others: G::ScalarField = (0..n).filter(|&k| k != real_idx).map(|k| c[k]).sum();
        c[real_idx] = ch - sum_others;
        s1[real_idx] = r1 + c[real_idx] * w1;
        s2[real_idx] = r2 + c[real_idx] * w2;
        r1.zeroize();
        r2.zeroize();
        w1.zeroize();
        w2.zeroize();
        Self { c, s1, s2 }
    }

    pub fn verify(
        &self,
        y: G,
        bases1: &[G],
        base2: G,
        transcript: &mut MerlinTranscript,
    ) -> Result<()> {
        let n = bases1.len();
        if !(self.c.len() == n && self.s1.len() == n && self.s2.len() == n) {
            return Err(Error::ProofVerificationError(
                "CdsOr response length mismatch".to_string(),
            ));
        }
        let base2_table = BatchMulPreprocessing::<G::Group>::new(base2.into_group(), n);
        let y_table = BatchMulPreprocessing::<G::Group>::new(y.into_group(), n);
        let t = bases1
            .iter()
            .enumerate()
            .map(|(k, b1)| {
                *b1 * self.s1[k] + base2_table.windowed_mul(&self.s2[k])
                    - y_table.windowed_mul(&self.c[k])
            })
            .collect::<Vec<_>>();
        let t = G::Group::normalize_batch(&t);
        if self.c.iter().copied().sum::<G::ScalarField>()
            != Self::compute_challenge(y, bases1, base2, &t, transcript)
        {
            return Err(Error::ProofVerificationError(
                "CdsOr challenge mismatch".to_string(),
            ));
        }
        Ok(())
    }

    fn compute_challenge(
        y: G,
        bases1: &[G],
        base2: G,
        t: &[G],
        transcript: &mut MerlinTranscript,
    ) -> G::ScalarField {
        transcript.append(b"b2", &base2);
        transcript.append(b"y", &y);
        for b1 in bases1 {
            transcript.append(b"b1", b1);
        }
        for ti in t {
            transcript.append(b"t", ti);
        }
        transcript.challenge_scalar::<G::ScalarField>(b"c")
    }
}

/// This is the proof for mediator affirm/reject. A CDS ring over the mediator entry:
/// `ct_med = eph_pk_med_keys[k] * sk_enc^{-1} + sig_key_gen * sk_aff` for the mediator's own encryption-key index `k`.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorTxnProof<G: AffineRepr>(pub CdsOr<G>);

impl<G: AffineRepr> MediatorTxnProof<G> {
    /// `med_index` is the mediator's index in the leg encryption and `enc_key_index` is the index of its encryption
    /// key in [`MediatorEncryption::eph_pk_med_keys`]. `enc_key_index` is hidden by the ring and must not be revealed.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        mediator_sk: G::ScalarField,
        enc_sk: G::ScalarField,
        med_index: usize,
        enc_key_index: usize,
        accept: bool,
        nonce: &[u8],
        med: &MediatorEncryption<G>,
        sig_key_gen: G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        Self::new_with_given_transcript(
            rng,
            mediator_sk,
            enc_sk,
            med_index,
            enc_key_index,
            accept,
            nonce,
            med,
            sig_key_gen,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        mediator_sk: G::ScalarField,
        mut enc_sk: G::ScalarField,
        med_index: usize,
        enc_key_index: usize,
        accept: bool,
        nonce: &[u8],
        med: &MediatorEncryption<G>,
        sig_key_gen: G,
        transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        Self::add_to_transcript(transcript, accept, med_index, nonce);
        let enc_sk_inv = enc_sk.inverse().ok_or(Error::InvertingZero)?;
        Zeroize::zeroize(&mut enc_sk);
        // One ring branch per encryption key, sharing `sig_key_gen` and the ciphertext `ct_med`.
        Ok(Self(CdsOr::new(
            rng,
            enc_sk_inv,
            mediator_sk,
            enc_key_index,
            med.ct_med,
            &med.eph_pk_med_keys,
            sig_key_gen,
            transcript,
        )))
    }

    pub fn verify(
        &self,
        med_index: usize,
        accept: bool,
        nonce: &[u8],
        med: &MediatorEncryption<G>,
        sig_key_gen: G,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_LABEL);
        self.verify_with_given_transcript(
            med_index,
            accept,
            nonce,
            med,
            sig_key_gen,
            &mut transcript,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        med_index: usize,
        accept: bool,
        nonce: &[u8],
        med: &MediatorEncryption<G>,
        sig_key_gen: G,
        transcript: &mut MerlinTranscript,
    ) -> Result<()> {
        // The ring's extractor needs `mu_j != 0` to force the affirmer's encryption secret.
        if med.ct_med.is_zero() || med.eph_pk_med_keys.iter().any(|e| e.is_zero()) {
            return Err(Error::ProofVerificationError(
                "ct_med or eph_pk_med_keys is identity".to_string(),
            ));
        }
        Self::add_to_transcript(transcript, accept, med_index, nonce);
        self.0
            .verify(med.ct_med, &med.eph_pk_med_keys, sig_key_gen, transcript)
    }

    fn add_to_transcript(
        transcript: &mut MerlinTranscript,
        accept: bool,
        med_index: usize,
        nonce: &[u8],
    ) {
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }
        transcript.append_message(MEDIATOR_INDEX_LABEL, &(med_index as u32).to_le_bytes());
        transcript.append_message(NONCE_LABEL, nonce);
    }
}

/// This is the proof for mediator affirm/reject over a [`MediatorEncryptionOld`] entry, i.e. a leg
/// created before the broadcast scheme, where the affirmation key was encrypted to the single
/// encryption key at `enc_key_index`. Kept so those legs can still be affirmed; new legs use
/// [`MediatorTxnProof`]. Report section 5.1.12
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MediatorTxnOldProof<G: AffineRepr> {
    pub resp_enc_pk: PokPedersenCommitment<G>,
}

impl<G: AffineRepr> MediatorTxnOldProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: MediatorEncryptionOld<G>,
        enc_sk: G::ScalarField,
        mediator_sk: G::ScalarField,
        accept: bool,
        nonce: &[u8],
        sig_key_gen: &G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_OLD_LABEL);
        Self::new_with_given_transcript(
            rng,
            leg_enc,
            enc_sk,
            mediator_sk,
            accept,
            nonce,
            sig_key_gen,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        leg_enc: MediatorEncryptionOld<G>,
        mut enc_sk: G::ScalarField,
        mut mediator_sk: G::ScalarField,
        accept: bool,
        nonce: &[u8],
        sig_key_gen: &G,
        mut transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let y = leg_enc.ct_med;
        let eph_pk = &leg_enc.eph_pk_med_key;
        let enc_pk = PokPedersenCommitmentProtocol::init(
            enc_sk.inverse().ok_or(Error::InvertingZero)?,
            G::ScalarField::rand(rng),
            eph_pk,
            mediator_sk,
            G::ScalarField::rand(rng),
            sig_key_gen,
        );

        Zeroize::zeroize(&mut enc_sk);
        Zeroize::zeroize(&mut mediator_sk);

        enc_pk.challenge_contribution(eph_pk, sig_key_gen, &y, &mut transcript)?;

        add_to_transcript!(transcript, LEG_ENC_LABEL, leg_enc, NONCE_LABEL, nonce);

        let challenge =
            transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_OLD_CHALLENGE_LABEL);

        let resp_enc_pk = enc_pk.gen_proof(&challenge);
        Ok(Self { resp_enc_pk })
    }

    pub fn verify(
        &self,
        leg_enc: MediatorEncryptionOld<G>,
        accept: bool,
        nonce: &[u8],
        sig_key_gen: G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(MEDIATOR_TXN_OLD_LABEL);
        self.verify_with_given_transcript(leg_enc, accept, nonce, sig_key_gen, &mut transcript, rmc)
    }

    pub fn verify_with_given_transcript(
        &self,
        leg_enc: MediatorEncryptionOld<G>,
        accept: bool,
        nonce: &[u8],
        sig_key_gen: G,
        mut transcript: &mut MerlinTranscript,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        // Hash the mediator's response
        if accept {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
        } else {
            transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
        }

        let y = leg_enc.ct_med;
        let eph_pk = leg_enc.eph_pk_med_key;

        self.resp_enc_pk
            .challenge_contribution(&eph_pk, &sig_key_gen, &y, &mut transcript)?;

        add_to_transcript!(transcript, LEG_ENC_LABEL, leg_enc, NONCE_LABEL, nonce);

        let challenge =
            transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_OLD_CHALLENGE_LABEL);

        verify_or_rmc_3!(
            rmc,
            self.resp_enc_pk,
            "resp_enc_pk verification failed",
            y,
            eph_pk,
            sig_key_gen,
            &challenge,
        );

        Ok(())
    }
}

/// This is the proof for mediator affirm/reject when asset-id is revealed. Since the mediator's
/// affirmation key is known to the verifier, this is a proof of knowledge of its secret key.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PublicAssetMediatorTxnProof<G: AffineRepr>(pub PokDiscreteLog<G>);

impl<G: AffineRepr> PublicAssetMediatorTxnProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        mediator_sk: G::ScalarField,
        accept: bool,
        nonce: &[u8],
        mediator_pk: &G,
        sig_key_gen: &G,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(PUBLIC_MEDIATOR_TXN_LABEL);
        Self::new_with_given_transcript(
            rng,
            mediator_sk,
            accept,
            nonce,
            mediator_pk,
            sig_key_gen,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        mut mediator_sk: G::ScalarField,
        accept: bool,
        nonce: &[u8],
        mediator_pk: &G,
        sig_key_gen: &G,
        transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        add_to_transcript(transcript, accept, nonce);
        let proto =
            PokDiscreteLogProtocol::init(mediator_sk, G::ScalarField::rand(rng), sig_key_gen);
        Zeroize::zeroize(&mut mediator_sk);
        proto.challenge_contribution(sig_key_gen, mediator_pk, &mut *transcript)?;
        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_RESPONSE_LABEL);
        Ok(Self(proto.gen_proof(&challenge)))
    }

    pub fn verify(
        &self,
        accept: bool,
        nonce: &[u8],
        mediator_pk: &G,
        sig_key_gen: &G,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(PUBLIC_MEDIATOR_TXN_LABEL);
        self.verify_with_given_transcript(
            accept,
            nonce,
            mediator_pk,
            sig_key_gen,
            &mut transcript,
            rmc,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        accept: bool,
        nonce: &[u8],
        mediator_pk: &G,
        sig_key_gen: &G,
        transcript: &mut MerlinTranscript,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        add_to_transcript(transcript, accept, nonce);
        self.0
            .challenge_contribution(sig_key_gen, mediator_pk, &mut *transcript)?;
        let challenge = transcript.challenge_scalar::<G::ScalarField>(MEDIATOR_TXN_RESPONSE_LABEL);
        match rmc {
            Some(rmc) => {
                self.0.verify_using_randomized_mult_checker(
                    *mediator_pk,
                    *sig_key_gen,
                    &challenge,
                    rmc,
                );
                Ok(())
            }
            None => self
                .0
                .verify(mediator_pk, sig_key_gen, &challenge)
                .map_err(|_| {
                    Error::ProofVerificationError(
                        "PublicAssetMediatorTxnProof verification failed".to_string(),
                    )
                }),
        }
    }
}

fn add_to_transcript(transcript: &mut MerlinTranscript, accept: bool, nonce: &[u8]) {
    if accept {
        transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_ACCEPT_RESPONSE);
    } else {
        transcript.append_message(MEDIATOR_TXN_RESPONSE_LABEL, MEDIATOR_TXN_REJECT_RESPONSE);
    }
    transcript.append_message(NONCE_LABEL, nonce);
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_serialize::CanonicalSerialize;
    use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
    use std::time::Instant;

    type PallasA = ark_pallas::Affine;
    type Fr = ark_pallas::Fr;

    fn keygen<R: CryptoRngCore>(rng: &mut R, base: PallasA) -> (Fr, PallasA) {
        let sk = Fr::rand(rng);
        (sk, (base * sk).into_affine())
    }

    fn encrypt_mediator<G: AffineRepr>(
        g: G,
        enc_keys: &[G],
        r: G::ScalarField,
        pk_aff: G,
    ) -> MediatorEncryption<G> {
        let mut proj = Vec::with_capacity(1 + enc_keys.len());
        proj.push(g * r + pk_aff);
        proj.extend(enc_keys.iter().map(|e| *e * r));
        let aff = G::Group::normalize_batch(&proj);
        MediatorEncryption {
            ct_med: aff[0],
            eph_pk_med_keys: aff[1..].to_vec(),
        }
    }

    #[test]
    fn mediator_ring() {
        let mut rng = rand::thread_rng();
        let g = hash_to_pallas(b"test", b"enc-key-gen").into_affine();
        let h = hash_to_pallas(b"test", b"sig-key-gen").into_affine();
        let n = 5usize;
        let enc: Vec<(Fr, PallasA)> = (0..n).map(|_| keygen(&mut rng, g)).collect();
        let enc_keys: Vec<PallasA> = enc.iter().map(|(_, p)| *p).collect();
        let (sigma, pk_aff) = keygen(&mut rng, h);
        let mu = Fr::rand(&mut rng);
        let med = encrypt_mediator(g, &enc_keys, mu, pk_aff);

        // Ring affirms from the real key at 2 for the mediator at slot 1.
        let k_ = 2;
        let slot = 1;
        let nonce = b"leg-nonce";
        let pr = MediatorTxnProof::new(&mut rng, sigma, enc[k_].0, slot, k_, true, nonce, &med, h)
            .unwrap();
        assert!(pr.verify(slot, true, nonce, &med, h).is_ok());
        // An accept proof must not verify as a reject, under a different nonce, nor at another slot.
        assert!(pr.verify(slot, false, nonce, &med, h).is_err());
        assert!(pr.verify(slot, true, b"other-nonce", &med, h).is_err());
        assert!(pr.verify(slot + 1, true, nonce, &med, h).is_err());

        // Wrong affirmation secret must fail.
        let wrong_med_sk = Fr::rand(&mut rng);
        let bad = MediatorTxnProof::new(
            &mut rng,
            wrong_med_sk,
            enc[k_].0,
            slot,
            k_,
            true,
            nonce,
            &med,
            h,
        )
        .unwrap();
        assert!(bad.verify(slot, true, nonce, &med, h).is_err());
        // Affirming from a key the mediator does not hold must fail.
        let wrong_enc_sk = Fr::rand(&mut rng);
        let bad2 =
            MediatorTxnProof::new(&mut rng, sigma, wrong_enc_sk, slot, 0, true, nonce, &med, h)
                .unwrap();
        assert!(bad2.verify(slot, true, nonce, &med, h).is_err());

        // Identity not allowed
        let mut identity_med = med.clone();
        identity_med.eph_pk_med_keys[0] = PallasA::zero();
        assert!(pr.verify(slot, true, nonce, &identity_med, h).is_err());
    }

    /// Builds the pre-broadcast mediator entry directly: the current `Leg::encrypt` only produces
    /// the broadcast form, so a leg of the old shape has to be faked here.
    fn encrypt_mediator_old<G: AffineRepr>(
        g: G,
        enc_key: G,
        enc_key_index: u8,
        r: G::ScalarField,
        pk_aff: G,
    ) -> MediatorEncryptionOld<G> {
        let aff = G::Group::normalize_batch(&[g * r + pk_aff, enc_key * r]);
        MediatorEncryptionOld {
            enc_key_index,
            ct_med: aff[0],
            eph_pk_med_key: aff[1],
        }
    }

    #[test]
    fn mediator_old_action() {
        let mut rng = rand::thread_rng();
        let g = hash_to_pallas(b"test", b"enc-key-gen").into_affine();
        let h = hash_to_pallas(b"test", b"sig-key-gen").into_affine();
        let nonce = b"test-nonce";

        let (enc_sk, enc_pk) = keygen(&mut rng, g);
        let (sigma, pk_aff) = keygen(&mut rng, h);
        let r = Fr::rand(&mut rng);
        let med = encrypt_mediator_old(g, enc_pk, 0, r, pk_aff);

        // The mediator recovers its affirmation key from the single encryption key it has.
        assert_eq!(med.affirmation_key(&enc_sk).unwrap(), pk_aff);

        for accept in [true, false] {
            let pr =
                MediatorTxnOldProof::new(&mut rng, med.clone(), enc_sk, sigma, accept, nonce, &h)
                    .unwrap();
            assert!(pr.verify(med.clone(), accept, nonce, h, None).is_ok());

            let mut rmc = RandomizedMultChecker::new(Fr::rand(&mut rng));
            assert!(
                pr.verify(med.clone(), accept, nonce, h, Some(&mut rmc))
                    .is_ok()
            );
            assert!(rmc.verify().is_ok());

            // Must not verify as the opposite decision nor under a different nonce.
            assert!(pr.verify(med.clone(), !accept, nonce, h, None).is_err());
            assert!(
                pr.verify(med.clone(), accept, b"other-nonce", h, None)
                    .is_err()
            );
        }

        // Wrong affirmation secret must fail.
        let wrong_med_sk = Fr::rand(&mut rng);
        let bad =
            MediatorTxnOldProof::new(&mut rng, med.clone(), enc_sk, wrong_med_sk, true, nonce, &h)
                .unwrap();
        assert!(bad.verify(med.clone(), true, nonce, h, None).is_err());

        // Affirming with an encryption key the mediator does not hold must fail.
        let wrong_enc_sk = Fr::rand(&mut rng);
        let bad2 =
            MediatorTxnOldProof::new(&mut rng, med.clone(), wrong_enc_sk, sigma, true, nonce, &h)
                .unwrap();
        assert!(bad2.verify(med, true, nonce, h, None).is_err());
    }

    #[test]
    fn public_asset_mediator_action() {
        let mut rng = rand::thread_rng();
        let h = hash_to_pallas(b"test", b"sig-key-gen").into_affine();
        let nonce = b"test-nonce";
        let (sigma, pk_aff) = keygen(&mut rng, h);

        for accept in [true, false] {
            let pr = PublicAssetMediatorTxnProof::new(&mut rng, sigma, accept, nonce, &pk_aff, &h)
                .unwrap();
            assert!(pr.verify(accept, nonce, &pk_aff, &h, None).is_ok());

            let mut rmc = RandomizedMultChecker::new(Fr::rand(&mut rng));
            assert!(
                pr.verify(accept, nonce, &pk_aff, &h, Some(&mut rmc))
                    .is_ok()
            );
            assert!(rmc.verify().is_ok());

            // Must not verify as the opposite decision, under a different nonce, nor for another key.
            assert!(pr.verify(!accept, nonce, &pk_aff, &h, None).is_err());
            assert!(
                pr.verify(accept, b"other-nonce", &pk_aff, &h, None)
                    .is_err()
            );
            let (_, other_pk) = keygen(&mut rng, h);
            assert!(pr.verify(accept, nonce, &other_pk, &h, None).is_err());
        }

        // Wrong secret key must fail.
        let wrong_sk = Fr::rand(&mut rng);
        let bad =
            PublicAssetMediatorTxnProof::new(&mut rng, wrong_sk, true, nonce, &pk_aff, &h).unwrap();
        assert!(bad.verify(true, nonce, &pk_aff, &h, None).is_err());
    }

    #[test]
    fn mediator_ring_verification() {
        let mut rng = rand::thread_rng();
        let g = hash_to_pallas(b"test", b"enc-key-gen").into_affine();
        let h = hash_to_pallas(b"test", b"sig-key-gen").into_affine();
        let nonce = b"test-nonce";

        println!(" ring_n  m_med | proof bytes | prove us | verify us");
        for (n, m) in [(1usize, 1usize), (2, 4), (4, 4), (8, 8), (16, 8), (32, 8)] {
            let enc: Vec<(Fr, PallasA)> = (0..n).map(|_| keygen(&mut rng, g)).collect();
            let enc_keys: Vec<PallasA> = enc.iter().map(|(_, p)| *p).collect();
            let meds: Vec<(Fr, PallasA)> = (0..m).map(|_| keygen(&mut rng, h)).collect();
            let mus: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
            let entries: Vec<MediatorEncryption<PallasA>> = (0..m)
                .map(|j| encrypt_mediator(g, &enc_keys, mus[j], meds[j].1))
                .collect();

            let clock = Instant::now();
            let proofs: Vec<MediatorTxnProof<PallasA>> = (0..m)
                .map(|j| {
                    let k_star = j % n;
                    MediatorTxnProof::new(
                        &mut rng,
                        meds[j].0,
                        enc[k_star].0,
                        j,
                        k_star,
                        true,
                        nonce,
                        &entries[j],
                        h,
                    )
                    .unwrap()
                })
                .collect();
            let prove_us = clock.elapsed().as_micros();

            let clock = Instant::now();
            for j in 0..m {
                proofs[j].verify(j, true, nonce, &entries[j], h).unwrap();
            }
            let verify_us = clock.elapsed().as_micros();

            let size: usize = proofs.iter().map(|p| p.compressed_size()).sum();
            println!(
                "{:>6} {:>6} | {:>11} | {:>8} | {:>9}",
                n, m, size, prove_us, verify_us
            );
        }
    }
}
